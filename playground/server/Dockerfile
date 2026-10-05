# Built on the deployment host so that the image matches its architecture.
FROM eclipse-temurin:25-jdk-noble AS build

ARG SBT_VERSION=1.13.0
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && rm -rf /var/lib/apt/lists/* \
    && curl -fsSL "https://github.com/sbt/sbt/releases/download/v${SBT_VERSION}/sbt-${SBT_VERSION}.tgz" | tar xz -C /opt \
    && ln -s /opt/sbt/bin/sbt /usr/local/bin/sbt

WORKDIR /src
# Resolve dependencies in their own layer, so editing sources does not refetch the compiler.
COPY project/build.properties project/plugins.sbt ./project/
COPY build.sbt ./
RUN sbt -batch update

COPY src ./src
RUN sbt -batch stage

FROM eclipse-temurin:25-jdk-noble

# Compiling a snippet runs its macros, so the process gets no more rights than it needs.
RUN useradd --system --no-create-home --uid 10001 playground
WORKDIR /app
COPY --from=build /src/target/universal/stage/ ./
# sbt-native-packager stages the launcher 0744, i.e. executable by its owner only.
RUN chmod 0755 bin/playground-server
USER playground

EXPOSE 8080
# The root filesystem is read-only at runtime; /tmp is the one writable mount.
ENV HOME=/tmp
ENV JAVA_OPTS="-Xmx2g"
ENTRYPOINT ["/app/bin/playground-server"]
