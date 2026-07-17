#!/usr/bin/env bash
# Runs one benchmark suite, or all of them. --dry-run does a single iteration
# without warmup (as in CI); otherwise the full JMH configuration applies (150
# warmup and 20 measurement iterations).
#
# --runs N repeats the whole selection N times, with runs as the outer loop
# (suites are interleaved)
#
# JMH results are written to <results-dir>/<run>/<suite>.json, where <run> is
# 0 for a dry run and 1..N for full runs.
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

if [[ "$DRY_RUN" == 1 && -n "$RUNS" ]]; then
  echo "error: --dry-run and --runs cannot be combined" >&2
  usage
fi
if [[ -n "$RUNS" && ! "$RUNS" =~ ^[1-9][0-9]*$ ]]; then
  echo "error: --runs expects a positive integer" >&2
  usage
fi

JMH_ARGS=""
RUN_IDS=($(seq 1 "${RUNS:-1}"))
if [[ "$DRY_RUN" == 1 ]]; then
  JMH_ARGS=" -wi 0 -i 1"
  RUN_IDS=(0)
fi

if [[ -z "$RESULTS_DIR" ]]; then
  RESULTS_DIR="$SCRIPT_DIR/results"
elif [[ "$RESULTS_DIR" != /* ]]; then
  # Relative paths are resolved from the invocation directory.
  RESULTS_DIR="$ORIG_PWD/$RESULTS_DIR"
fi
mkdir -p "$RESULTS_DIR"
RESULTS_DIR="$(cd "$RESULTS_DIR" && pwd)"
# Hidden files (e.g. macOS .DS_Store) do not count as content.
if [[ -n "$(ls "$RESULTS_DIR")" ]]; then
  echo "error: results directory is not empty: $RESULTS_DIR" >&2
  exit 1
fi

for suite in "${SUITES[@]}"; do
  check_suite "$suite"
done

for run in "${RUN_IDS[@]}"; do
  for suite in "${SUITES[@]}"; do
    echo "==> Run $run: $suite benchmarks..."
    mkdir -p "$RESULTS_DIR/$run"
    (cd "$suite" && sbt "bench / Jmh / run$JMH_ARGS -foe true -gc true -rf json -rff $RESULTS_DIR/$run/$suite.json")
  done
done
