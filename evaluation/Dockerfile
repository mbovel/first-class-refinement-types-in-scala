# Ready-to-run image for the benchmarks: first-class, stainless, and schmid.
#
# Contains JDK 25 (default), JDK 8 ($JDK8_HOME), sbt, git, Z3, the benchmark
# sources, prebuilt Stainless and refined-dotty jars, and warmed sbt caches,
# so the benchmarks run without further setup or network access.
#
# The Stainless native Z3 bindings are x86-64 only, so on ARM hosts (e.g.
# Apple Silicon) build and run with an explicit platform:
#
#   docker build --platform linux/amd64 -t refinement-bench evaluation
#   docker run --platform linux/amd64 refinement-bench --suite first-class --dry-run
#   docker run --platform linux/amd64 refinement-bench --suite stainless   # full run
#   docker run --platform linux/amd64 refinement-bench --suite all --dry-run
#
# The entry point is run.sh, which writes JMH results to
# /work/evaluation/results/<suite>.json; mount a host directory there to
# collect them:
#
#   docker run --platform linux/amd64 -v "$PWD/results:/work/evaluation/results" \
#     refinement-bench --suite all --dry-run
#
# For an interactive shell instead:
#
#   docker run --platform linux/amd64 --entrypoint bash -it refinement-bench
#
# JMH forks the benchmark JVMs with -Xmx8G: give the container >= 10 GB of
# memory.

FROM eclipse-temurin:8-jdk AS jdk8

FROM eclipse-temurin:25-jdk-noble

# JDK 8, used by schmid/setup.sh (via JDK8_HOME) to build refined-dotty with
# sbt 0.13, and by JMH's -jvm option to run the schmid benchmarks.
COPY --from=jdk8 /opt/java/openjdk /opt/java/jdk8
ENV JDK8_HOME=/opt/java/jdk8

RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git z3 \
    && rm -rf /var/lib/apt/lists/*

# sbt runner (fetches each project's exact sbt version on first use)
ARG SBT_VERSION=1.12.6
RUN curl -fsSL "https://github.com/sbt/sbt/releases/download/v${SBT_VERSION}/sbt-${SBT_VERSION}.tgz" \
      | tar xz -C /opt \
    && ln -s /opt/sbt/bin/sbt /usr/local/bin/sbt

WORKDIR /work/evaluation

# Build the vendored Stainless compiler plugin (slow, changes rarely, so it
# comes first: later changes to the benchmarks do not invalidate this layer).
COPY stainless/stainless stainless/stainless
COPY stainless/setup.sh stainless/setup.sh
RUN cd stainless && ./setup.sh

# Build Georg Schmid's LiquidTyper-enabled Dotty fork.
COPY schmid/refined-dotty schmid/refined-dotty
COPY schmid/setup.sh schmid/setup.sh
RUN cd schmid && ./setup.sh

# Benchmark sources and harnesses.
COPY sources sources
COPY first-class first-class
COPY stainless/bench stainless/bench
COPY stainless/build.sbt stainless/build.sbt
COPY stainless/project stainless/project
COPY schmid/src schmid/src
COPY schmid/build.sbt schmid/build.sbt
COPY schmid/project schmid/project

# Compile the benchmark harnesses (including JMH codegen) to warm the caches.
RUN cd first-class && sbt "bench / Jmh / compile"
RUN cd stainless && sbt "bench / Jmh / compile"
RUN cd schmid && sbt "bench / Jmh / compile"

COPY run.sh run.sh
ENTRYPOINT ["/work/evaluation/run.sh"]
