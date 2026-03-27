#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

echo "==> Initializing stainless submodule..."
git -C "$(git rev-parse --show-toplevel)" submodule update --init --recursive evaluation/first_class_and_stainless/stainless

echo "==> Building Stainless assembly jar..."
cd stainless
sbt "stainless-dotty / assembly" "stainless-library / package"
cd "$SCRIPT_DIR"

echo "==> Copying jars to lib/..."
mkdir -p lib
cp stainless/frontends/dotty/target/scala-*/stainless-dotty-assembly*.jar lib/stainless-assembly.jar
cp stainless/frontends/library/target/scala-*/stainless-library*.jar lib/stainless-library.jar

echo "==> Done. Jars are in lib/:"
ls -lh lib/
