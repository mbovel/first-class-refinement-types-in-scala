#!/usr/bin/env bash
# Build the source archive for conference-publishing.com or for arXiv.
#
# Usage: ./make-archive.sh [--arxiv] [<output.zip>]
#
# Includes the LaTeX sources, acmart.cls (the publisher's checker verifies
# its version and errors if it is absent; arXiv's own acmart may be older),
# and the .bbl, so neither side has to run BibTeX.
#
# --arxiv swaps two files: html-fixes.css is added, because paper.tex
# \lxRequireResource's it for the LaTeXML build behind arXiv's HTML view,
# and paper.pdf is left out, since arXiv compiles the sources itself and
# asks that the generated PDF not be submitted alongside them.
#
# Built from the CLI so no __MACOSX/AppleDouble junk ends up in the
# zip (Finder adds those).
set -euo pipefail

arxiv=false
if [[ "${1:-}" == "--arxiv" ]]; then
  arxiv=true
  shift
fi

out="${1:-paper-source.zip}"
cd "$(dirname "$0")"

files=(paper.tex appendix.tex references.bib acmart.cls bcprules.sty
       bench_table.tex fig-*.tex paper.bbl)
if $arxiv; then
  files+=(html-fixes.css)
else
  files+=(paper.pdf)
fi

rm -f "$out"
zip -X -q "$out" "${files[@]}"
unzip -l "$out"
