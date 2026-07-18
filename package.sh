#!/usr/bin/env bash
# Prepares the Zenodo artifact archive: the repository (without .git and
# build residue) plus the saved Docker image, as a single zip.
#
# The Docker image is stored as a plain `docker save` tar; the zip's own
# compression is applied once, and evaluators load it directly after
# unzipping with `docker load -i artifact-image.tar`.
#
# Requires the image to be built first:
#
#   docker build --platform linux/amd64 -t refinement-artifact .
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

NAME=first-class-refinement-types
OUT_DIR="$SCRIPT_DIR/artifact"
STAGING="$OUT_DIR/$NAME"

if ! docker image inspect refinement-artifact >/dev/null 2>&1; then
  echo "error: refinement-artifact image not found; build it first:" >&2
  echo "  docker build --platform linux/amd64 -t refinement-artifact ." >&2
  exit 1
fi

echo "==> Staging repository (without .git and build residue)..."
rm -rf "$STAGING"
mkdir -p "$STAGING"
rsync -a \
  --exclude '.git' \
  --exclude 'target' \
  --exclude '.bsp' \
  --exclude '.bloop' \
  --exclude '.metals' \
  --exclude '.scala-build' \
  --exclude '.stainless-cache' \
  --exclude '.DS_Store' \
  --exclude 'smt-sessions' \
  --exclude '/artifact' \
  --exclude '/paper/*.aux' \
  --exclude '/paper/*.log' \
  --exclude '/paper/*.fls' \
  --exclude '/paper/*.fdb_latexmk' \
  --exclude '/paper/*.blg' \
  --exclude '/paper/*.out' \
  --exclude '/paper/*.synctex.gz' \
  --exclude '/paper/paper-diff.*' \
  --exclude '/implementation/out' \
  --exclude '/evaluation/stainless/lib' \
  --exclude '/evaluation/results' \
  --exclude '/evaluation/first-class/bench/out' \
  --exclude '/evaluation/stainless/bench/out' \
  --exclude '/evaluation/schmid/out' \
  ./ "$STAGING/"

# evaluation/schmid/lib is deliberately included: the jars are small, pure
# JVM (platform-independent), and their from-source build depends on the old
# Typesafe resolver, so shipping them is insurance against repository rot.
# The Stainless jars are NOT included: they embed per-platform Z3 natives and
# are already in the Docker image.
if [[ ! -e "$STAGING/evaluation/schmid/lib/dotty_2.11-0.1-SNAPSHOT.jar" ]]; then
  echo "warn: evaluation/schmid/lib is not populated; run evaluation/schmid/setup.sh first to include the refined-dotty jars" >&2
fi

echo "==> Recording version..."
git rev-parse HEAD > "$STAGING/VERSION"

echo "==> Saving Docker image..."
docker save refinement-artifact -o "$STAGING/artifact-image.tar"

echo "==> Creating zip..."
cd "$OUT_DIR"
rm -f "$NAME.zip"
zip -r -q "$NAME.zip" "$NAME"
rm -rf "$STAGING"

echo "==> Done:"
ls -lh "$OUT_DIR/$NAME.zip"
