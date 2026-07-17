# Toolchain for running all benchmarks: first-class, stainless, and schmid.
#
# The image contains JDK 25 (default), JDK 8 (as $JDK8_HOME, needed by the
# refined-dotty build and the schmid JMH forks), sbt, git, and Z3. The
# repository itself is volume-mounted, so jars built by the setup scripts and
# benchmark results persist on the host.
#
# The Stainless native Z3 bindings are x86-64 only, so on ARM hosts (e.g.
# Apple Silicon) build and run with an explicit platform:
#
#   docker build --platform linux/amd64 -t refinement-bench evaluation
#   docker run --platform linux/amd64 -v "$PWD:/work" -w /work -it refinement-bench
#
# Then, inside the container, e.g.:
#
#   cd evaluation/first-class && sbt 'bench / Jmh / run -wi 0 -i 1 FirstClassBenchmarks'
#   cd evaluation/stainless   && ./setup.sh && sbt 'bench / Jmh / run -wi 0 -i 1 StainlessVerifyBenchmarks'
#   cd evaluation/schmid      && ./setup.sh && sbt 'Jmh / run -wi 0 -i 1 SchmidRefinementBenchmarks -jvm '"$JDK8_HOME/bin/java"
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

WORKDIR /work
CMD ["bash"]
