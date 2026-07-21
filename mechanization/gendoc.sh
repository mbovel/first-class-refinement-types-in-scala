#!/usr/bin/env bash
# Generate coqdoc HTML for the mechanization into public/website/mechanization.
# Uses coqdocjs (submodule in coqdocjs/) for unicode display and proof hiding.
set -euo pipefail

cd "$(dirname "$0")"

[ -f coqdocjs/extra/header.html ] || git -C .. submodule update --init mechanization/coqdocjs

make refinement_types/Makefile

# Paths are relative to refinement_types/, where coqdoc is invoked.
export COQDOCFLAGS="\
  --toc --toc-depth 2 --html --interpolate --utf8 \
  --index indexpage --no-lib-name --parse-comments \
  --with-header ../coqdocjs/extra/header.html \
  --with-footer ../coqdocjs/extra/footer.html"
rm -rf refinement_types/html
make -C refinement_types html

out=../website/mechanization
rm -rf "$out"
mkdir -p "$(dirname "$out")"
cp -R refinement_types/html "$out"
cp -R coqdocjs/extra/resources "$out"

echo "Documentation generated in $(cd "$out" && pwd)"
