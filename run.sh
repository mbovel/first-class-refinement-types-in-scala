#!/usr/bin/env bash
# Entry point for the artifact image (also runnable directly from a checkout).
#
#   run.sh                                 getting-started run: check the proofs, compile an
#                                          example, then dry-run all benchmarks
#   run.sh mechanization                   compile the mechanization
#   run.sh evaluation bench ARGS...        run the benchmarks (delegates to evaluation/run.sh)
#   run.sh evaluation make-table ARGS...   regenerate the results table (evaluation/make_table.py)
#   run.sh implementation SBT_ARGS...      run sbt in the qualified-types compiler checkout
set -euo pipefail

cd "$(dirname "$0")"

usage() {
  echo "Usage: $(basename "$0") [mechanization | evaluation bench|make-table ARGS... | implementation SBT_ARGS...]" >&2
  echo "With no arguments: check the mechanization proofs, compile an example with the" >&2
  echo "qualified-types compiler, then dry-run all benchmark suites." >&2
  exit "${1:-1}"
}

banner() {
  echo
  echo "======================================================================"
  echo "  $1"
  echo "======================================================================"
  echo
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
    banner "📜 [1/3] Mechanization — checking the Rocq proofs"
    make_mechanization
    banner "🛠️  [2/3] Implementation — compiling an example with qualified types"
    (cd implementation && sbt "scala3-bootstrapped / scalac -language:experimental.qualifiedTypes tests/pos-custom-args/qualified-types/list_collect.scala")
    banner "⏱️  [3/3] Evaluation — dry-running all benchmark suites (1 iteration, no warmup)"
    ./evaluation/run.sh --suite all --dry-run
    banner "✅ Done: proofs checked, example compiled, benchmarks dry-run complete"
    ;;
  mechanization)
    [[ $# -eq 1 ]] || usage
    make_mechanization
    ;;
  evaluation)
    shift
    case "${1:-}" in
      bench)
        shift
        ./evaluation/run.sh "$@"
        ;;
      make-table)
        shift
        python3 ./evaluation/make_table.py "$@"
        ;;
      *)
        echo "error: evaluation expects a subcommand: bench or make-table" >&2
        usage
        ;;
    esac
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
