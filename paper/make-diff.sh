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

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# Inline \input'd figures ourselves so their changes are diffed too. We do
# not use latexdiff --flatten: it also inlines the .bbl (yielding spurious
# warnings) and mis-hashes \lstinline commands in the flattened document,
# producing a diff that does not compile.
cat > "$tmp/flatten.pl" <<'EOF'
# Inline \input{...} commands (up to 3 levels), resolving relative to the
# file's directory. Commented-out \input lines are left untouched.
use strict; use warnings;
use File::Basename;

sub slurp {
  my ($path) = @_;
  open my $fh, "<", $path or die "cannot open $path: $!";
  local $/; my $c = <$fh>; close $fh;
  return $c;
}

sub inline_input {
  my ($dir, $name) = @_;
  my $f = "$dir/$name";
  $f .= ".tex" unless $f =~ /\.tex$/;
  return slurp($f);
}

my ($file) = @ARGV;
my $dir = dirname($file);
my $text = slurp($file);
for (1 .. 3) {
  last unless $text =~ s{^[ \t]*\\input\{([^\}]+)\}}{inline_input($dir, $1)}gme;
}
print $text;
EOF

# Extract the old paper sources at the given revision, then flatten both.
git -C "$repo_root" archive "$rev" paper | tar -x -C "$tmp"
perl "$tmp/flatten.pl" "$tmp/paper/paper.tex" > "$tmp/old-flat.tex"
perl "$tmp/flatten.pl" "$paper_dir/paper.tex" > "$tmp/new-flat.tex"

# lstlisting is registered as a verbatim environment so that changed
# listings are marked up as a whole instead of latexdiff injecting \DIF
# commands into the code. acks is registered too: it is a comment-package
# environment whose \end{acks} must start a line, which latexdiff markup
# would otherwise break.
"${latexdiff[@]}" \
  --config 'VERBATIMENV=(?:verbatim[*]?|lstlisting|acks)' \
  "$tmp/old-flat.tex" "$tmp/new-flat.tex" > "$paper_dir/$out"

echo "Wrote $paper_dir/$out (diff against $rev)"
