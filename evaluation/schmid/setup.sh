#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

# Skip submodule init when the sources are already present (e.g. in the
# Docker image build, where there is no enclosing git repository).
if [[ -e refined-dotty/project/Build.scala ]]; then
  echo "==> refined-dotty sources already present, skipping submodule init"
else
  echo "==> Initializing refined-dotty submodule..."
  git -C "$(git rev-parse --show-toplevel)" submodule update --init evaluation/schmid/refined-dotty
fi

# The refined-dotty build uses sbt 0.13, which requires JDK 8.
if [[ -n "${JDK8_HOME:-}" ]]; then
  export JAVA_HOME="$JDK8_HOME"
  export PATH="$JAVA_HOME/bin:$PATH"
elif ! java -version 2>&1 | grep -q '"1\.8'; then
  if command -v cs >/dev/null 2>&1; then
    echo "==> Switching to JDK 8 via coursier..."
    # coursier's env snippet reads $JAVA_HOME before setting it; define it so
    # the bare reference survives `set -u`.
    export JAVA_HOME="${JAVA_HOME:-}"
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
# The Ivy cache may be relocated via SBT_OPTS/JAVA_OPTS (e.g. to a local disk
# instead of an NFS home); honor those overrides like sbt does.
IVY_HOME="$HOME/.ivy2"
prev=
for tok in ${SBT_OPTS:-} ${JAVA_OPTS:-}; do
  case "$tok" in
    -Dsbt.ivy.home=*|-Divy.home=*) IVY_HOME="${tok#*=}" ;;
  esac
  if [[ "$prev" == "--ivy" || "$prev" == "-ivy" ]]; then
    IVY_HOME="$tok"
  fi
  prev="$tok"
done
cp "$IVY_HOME/cache/org.scala-sbt/interface/jars/interface-0.13.11.jar" lib/

echo "==> Done. Jars are in lib/:"
ls -lh lib/
