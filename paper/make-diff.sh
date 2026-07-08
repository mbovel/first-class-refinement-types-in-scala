#!/usr/bin/env bash
# Generate a latexdiff of the paper against a given git revision.
#
# Usage: ./make-diff.sh [<git-rev>] [<output.tex>]
#
# Defaults: rev = oopsla-2026-initial (the submitted version),
#           output = paper-diff.tex (in this directory).
#
# The output file is a regular LaTeX document with additions/deletions
# marked up; compile it like paper.tex to get a visual diff.
set -euo pipefail

rev="${1:-oopsla-2026-initial}"
out="${2:-paper-diff.tex}"

paper_dir="$(cd "$(dirname "$0")" && pwd)"
repo_root="$(git -C "$paper_dir" rev-parse --show-toplevel)"

# This TeX Live install ships latexdiff.pl without a bin symlink.
if command -v latexdiff >/dev/null 2>&1; then
  latexdiff=(latexdiff)
else
  latexdiff=(perl "$(kpsewhich --format=texmfscripts latexdiff.pl)")
fi

# Extract the old paper sources at the given revision.
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
git -C "$repo_root" archive "$rev" paper | tar -x -C "$tmp"

# --flatten inlines \input'd figures so their changes are diffed too.
# lstlisting is registered as a verbatim environment so that changed
# listings are marked up as a whole instead of latexdiff injecting \DIF
# commands into the code.
"${latexdiff[@]}" --flatten \
  --config 'VERBATIMENV=(?:verbatim[*]?|lstlisting)' \
  "$tmp/paper/paper.tex" "$paper_dir/paper.tex" > "$paper_dir/$out"

echo "Wrote $paper_dir/$out (diff against $rev)"
