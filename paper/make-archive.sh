#!/usr/bin/env bash
# Build the source archive for conference-publishing.com.
#
# Usage: ./make-archive.sh [<output.zip>]
#
# Includes the LaTeX sources, acmart.cls (the checker verifies its
# version and errors if it is absent), and the compiled PDF and .bbl.
# Built from the CLI so no __MACOSX/AppleDouble junk ends up in the
# zip (Finder adds those).
set -euo pipefail

out="${1:-paper-source.zip}"
cd "$(dirname "$0")"

rm -f "$out"
zip -X -q "$out" paper.tex references.bib acmart.cls bcprules.sty \
    bench_table.tex fig-*.tex paper.bbl paper.pdf
unzip -l "$out"
