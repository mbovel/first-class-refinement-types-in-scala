#!/usr/bin/env bash
# Runs one benchmark suite, or all of them. --dry-run does a single iteration
# without warmup (as in CI); otherwise the full JMH configuration applies (150
# warmup and 20 measurement iterations).
#
# --runs N repeats the whole selection N times, with runs as the outer loop
# (suites are interleaved)
#
# JMH results are written to <results-dir>/<suite>/<run>.json, where <run> is
# the date and time at which that suite's run started (e.g. 2026-07-18-2200,
# with a -dry suffix for dry runs), so results from separate invocations
# accumulate side by side.
set -euo pipefail

usage() {
  echo "Usage: $(basename "$0") --suite first-class|stainless|schmid|all [--dry-run | --runs N] [--results-dir DIR]" >&2
  exit 1
}

ORIG_PWD="$PWD"
SUITE=""
DRY_RUN=0
RUNS=""
RESULTS_DIR=""
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
    --runs)
      [[ $# -ge 2 ]] || usage
      RUNS="$2"
      shift 2
      ;;
    --results-dir)
      [[ $# -ge 2 ]] || usage
      RESULTS_DIR="$2"
      shift 2
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
    SUITES=(stainless schmid first-class)
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

if [[ "$DRY_RUN" == 1 && -n "$RUNS" ]]; then
  echo "error: --dry-run and --runs cannot be combined" >&2
  usage
fi
if [[ -n "$RUNS" && ! "$RUNS" =~ ^[1-9][0-9]*$ ]]; then
  echo "error: --runs expects a positive integer" >&2
  usage
fi

JMH_ARGS=""
N_RUNS="${RUNS:-1}"
if [[ "$DRY_RUN" == 1 ]]; then
  JMH_ARGS=" -wi 0 -i 1"
fi

if [[ -z "$RESULTS_DIR" ]]; then
  RESULTS_DIR="$SCRIPT_DIR/results"
elif [[ "$RESULTS_DIR" != /* ]]; then
  # Relative paths are resolved from the invocation directory.
  RESULTS_DIR="$ORIG_PWD/$RESULTS_DIR"
fi
mkdir -p "$RESULTS_DIR"
RESULTS_DIR="$(cd "$RESULTS_DIR" && pwd)"

for suite in "${SUITES[@]}"; do
  check_suite "$suite"
done

for ((run = 1; run <= N_RUNS; run++)); do
  for suite in "${SUITES[@]}"; do
    RUN_ID="$(date +%Y-%m-%d-%H%M)"
    if [[ "$DRY_RUN" == 1 ]]; then
      RUN_ID="$RUN_ID-dry"
    fi
    echo "==> Run $run: $suite benchmarks ($RUN_ID)..."
    mkdir -p "$RESULTS_DIR/$suite"
    (cd "$suite" && sbt "clean; bench / Jmh / run$JMH_ARGS -foe true -gc true -rf json -rff $RESULTS_DIR/$suite/$RUN_ID.json")
  done
done
