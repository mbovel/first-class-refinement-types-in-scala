#!/usr/bin/env bash
# Entry point for the artifact image (also runnable directly from a checkout).
#
#   run.sh                            compile the mechanization, then dry-run all benchmarks
#   run.sh mechanization              compile the mechanization
#   run.sh evaluation ARGS...         run the benchmarks (delegates to evaluation/run.sh)
#   run.sh implementation SBT_ARGS... run sbt in the qualified-types compiler checkout
set -euo pipefail

cd "$(dirname "$0")"

usage() {
  echo "Usage: $(basename "$0") [mechanization | evaluation ARGS... | implementation SBT_ARGS...]" >&2
  echo "With no arguments: compile the mechanization, then dry-run all benchmarks." >&2
  exit "${1:-1}"
}

make_mechanization() {
  # Use the ambient Rocq when on PATH; otherwise go through opam (as in the
  # Docker image, where the toolchain lives in the rocq user's opam switch).
  if command -v rocq >/dev/null 2>&1; then
    make -C mechanization
  else
    opam exec -- make -C mechanization
  fi
}

case "${1:-}" in
  "")
    make_mechanization
    ./evaluation/run.sh --suite all --dry-run
    ;;
  mechanization)
    [[ $# -eq 1 ]] || usage
    make_mechanization
    ;;
  evaluation)
    shift
    ./evaluation/run.sh "$@"
    ;;
  implementation)
    shift
    (cd implementation && sbt "$@")
    ;;
  -h|--help)
    usage 0
    ;;
  *)
    echo "error: unknown command: $1" >&2
    usage
    ;;
esac
