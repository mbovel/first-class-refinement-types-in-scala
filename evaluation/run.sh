#!/usr/bin/env bash
# Runs one benchmark suite, or all of them. --dry-run does a single iteration
# without warmup (as in CI); otherwise the full JMH configuration applies (150
# warmup and 20 measurement iterations). JMH results are written to
# results/<suite>.json.
set -euo pipefail

usage() {
  echo "Usage: $(basename "$0") --suite first-class|stainless|schmid|all [--dry-run]" >&2
  exit 1
}

SUITE=""
DRY_RUN=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --suite)
      [[ $# -ge 2 ]] || usage
      SUITE="$2"
      shift 2
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    -h|--help)
      usage
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage
      ;;
  esac
done

case "$SUITE" in
  first-class|stainless|schmid)
    SUITES=("$SUITE")
    ;;
  all)
    SUITES=(first-class stainless schmid)
    ;;
  "")
    usage
    ;;
  *)
    echo "error: unknown suite: $SUITE" >&2
    usage
    ;;
esac

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

check_suite() {
  case "$1" in
    stainless)
      if [[ ! -e stainless/lib/stainless-assembly.jar ]]; then
        echo "error: Stainless jars not found; run stainless/setup.sh first" >&2
        exit 1
      fi
      ;;
    schmid)
      if [[ ! -e schmid/lib/dotty_2.11-0.1-SNAPSHOT.jar ]]; then
        echo "error: refined-dotty jars not found; run schmid/setup.sh first" >&2
        exit 1
      fi
      ;;
  esac
}

JMH_ARGS=""
if [[ "$DRY_RUN" == 1 ]]; then
  JMH_ARGS=" -wi 0 -i 1 -foe true"
fi

RESULTS_DIR="$SCRIPT_DIR/results"
mkdir -p "$RESULTS_DIR"

for suite in "${SUITES[@]}"; do
  check_suite "$suite"
done

for suite in "${SUITES[@]}"; do
  echo "==> Running $suite benchmarks..."
  (cd "$suite" && sbt "bench / Jmh / run$JMH_ARGS -rf json -rff $RESULTS_DIR/$suite.json")
done
