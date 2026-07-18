# Ready-to-run artifact image: the Rocq mechanization plus all benchmark
# suites (first-class, stainless, schmid).
#
# Build from the repository root:
#
#   docker build --platform linux/amd64 -t refinement-artifact .
#
# (The Stainless native Z3 bindings are x86-64 only, so on ARM hosts, e.g.
# Apple Silicon, the explicit platform is required.)
#
# The entry point is run.sh:
#
#   docker run refinement-artifact                  # everything: mechanization + all suites (dry run)
#   docker run refinement-artifact mechanization    # compile the mechanization only
#   docker run refinement-artifact evaluation --suite stainless --dry-run
#   docker run refinement-artifact evaluation --suite all --runs 10
#
# JMH results are written to /work/evaluation/results/<run>/<suite>.json;
# mount a host directory there to collect them:
#
#   docker run -v "$PWD/results:/work/evaluation/results" refinement-artifact
#
# For an interactive shell instead:
#
#   docker run --entrypoint bash -it refinement-artifact
#
# JMH forks the benchmark JVMs with -Xmx8G: give the container >= 10 GB of
# memory.

FROM eclipse-temurin:8-jdk AS jdk8
FROM eclipse-temurin:25-jdk-noble AS jdk25

# Rocq 9.2 with its OCaml/opam toolchain, user `rocq`.
FROM rocq/rocq-prover:9.2

# The base image uses a login shell whose profile resets PATH, which would
# hide the JDK installed below; use a plain shell instead. (Nothing at build
# time needs the opam environment; run.sh goes through `opam exec` at run
# time.)
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

USER root

# JDK 25 (default) and JDK 8, used by schmid/setup.sh (via JDK8_HOME) to
# build refined-dotty with sbt 0.13, and by JMH's -jvm option to run the
# schmid benchmarks.
COPY --from=jdk25 /opt/java/openjdk /opt/java/openjdk
COPY --from=jdk8 /opt/java/openjdk /opt/java/jdk8
ENV JAVA_HOME=/opt/java/openjdk
ENV JDK8_HOME=/opt/java/jdk8
ENV PATH=/opt/java/openjdk/bin:$PATH

# z3 is the external solver binary used by the schmid benchmarks; libgomp1 is
# required by the ScalaZ3 JNI library (libscalaz3.so links OpenMP) — without
# it, native Z3 fails to load and inox falls back to another solver.
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git z3 libgomp1 \
    && rm -rf /var/lib/apt/lists/*

# sbt runner (fetches each project's exact sbt version on first use)
ARG SBT_VERSION=1.12.6
RUN curl -fsSL "https://github.com/sbt/sbt/releases/download/v${SBT_VERSION}/sbt-${SBT_VERSION}.tgz" \
      | tar xz -C /opt \
    && ln -s /opt/sbt/bin/sbt /usr/local/bin/sbt

RUN mkdir /work && chown rocq:rocq /work
USER rocq
WORKDIR /work

# Build the vendored Stainless compiler plugin (slow, changes rarely, so it
# comes first: later changes to the benchmarks do not invalidate this layer).
COPY --chown=rocq:rocq evaluation/stainless/stainless evaluation/stainless/stainless
COPY --chown=rocq:rocq evaluation/stainless/setup.sh evaluation/stainless/setup.sh
RUN cd evaluation/stainless && ./setup.sh

# Build Georg Schmid's LiquidTyper-enabled Dotty fork.
COPY --chown=rocq:rocq evaluation/schmid/refined-dotty evaluation/schmid/refined-dotty
COPY --chown=rocq:rocq evaluation/schmid/setup.sh evaluation/schmid/setup.sh
RUN cd evaluation/schmid && ./setup.sh

# Benchmark sources and harnesses.
COPY --chown=rocq:rocq evaluation/sources evaluation/sources
COPY --chown=rocq:rocq evaluation/first-class evaluation/first-class
COPY --chown=rocq:rocq evaluation/stainless/bench evaluation/stainless/bench
COPY --chown=rocq:rocq evaluation/stainless/build.sbt evaluation/stainless/build.sbt
COPY --chown=rocq:rocq evaluation/stainless/project evaluation/stainless/project
COPY --chown=rocq:rocq evaluation/schmid/src evaluation/schmid/src
COPY --chown=rocq:rocq evaluation/schmid/build.sbt evaluation/schmid/build.sbt
COPY --chown=rocq:rocq evaluation/schmid/project evaluation/schmid/project

# Compile the benchmark harnesses (including JMH codegen) to warm the caches.
RUN cd evaluation/first-class && sbt "bench / Jmh / compile"
RUN cd evaluation/stainless && sbt "bench / Jmh / compile"
RUN cd evaluation/schmid && sbt "bench / Jmh / compile"

COPY --chown=rocq:rocq evaluation/stainless/stainless.conf evaluation/stainless/stainless.conf
COPY --chown=rocq:rocq evaluation/run.sh evaluation/run.sh

# Mechanization sources; the proofs are checked at run time (exit code 0 =
# everything compiles).
COPY --chown=rocq:rocq mechanization mechanization

COPY --chown=rocq:rocq run.sh run.sh
ENTRYPOINT ["/work/run.sh"]
