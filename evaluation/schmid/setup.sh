#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

echo "==> Initializing refined-dotty submodule..."
git -C "$(git rev-parse --show-toplevel)" submodule update --init evaluation/schmid/refined-dotty

# The refined-dotty build uses sbt 0.13, which requires JDK 8.
if [[ -n "${JDK8_HOME:-}" ]]; then
  export JAVA_HOME="$JDK8_HOME"
  export PATH="$JAVA_HOME/bin:$PATH"
elif ! java -version 2>&1 | grep -q '"1\.8'; then
  if command -v cs >/dev/null 2>&1; then
    echo "==> Switching to JDK 8 via coursier..."
    eval "$(cs java --jvm temurin:8 --env)"
  else
    echo "error: JDK 8 is required to build refined-dotty (set JDK8_HOME or install coursier)" >&2
    exit 1
  fi
fi
java -version

echo "==> Building refined-dotty jars..."
(cd refined-dotty && sbt dotty-interfaces/package package)

echo "==> Copying jars to lib/..."
mkdir -p lib
cp refined-dotty/target/scala-2.11/dotty_2.11-0.1-SNAPSHOT.jar lib/
cp refined-dotty/interfaces/target/dotty-interfaces-0.1-SNAPSHOT.jar lib/
cp refined-dotty/lib/leon_2.11-3.0.jar refined-dotty/lib/scala-smtlib_2.11.jar lib/
# sbt interface jar: resolved into the local Ivy cache by the refined-dotty
# build above; not available on Maven Central, so ship it in lib/ too.
cp "$HOME/.ivy2/cache/org.scala-sbt/interface/jars/interface-0.13.11.jar" lib/

echo "==> Done. Jars are in lib/:"
ls -lh lib/
