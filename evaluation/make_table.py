#!/usr/bin/env python3
"""
Generate the benchmark results table comparing compilation times across:
- First-class: first-class refinement types on Scala 3.8 vs. unchecked baseline
- Schmid: Georg Schmid's liquid types on Dotty 0.1 vs. unchecked baseline
- Stainless: Stainless with verification vs. contract-free sources compiled
  with the same Dotty, without the Stainless plugin

Reads JMH JSON results from <results-dir>/<suite>/<run>.json as written by
run.sh. Each JMH fork (one JVM invocation) is reduced to its mean, and the
reported score and 95% confidence interval are computed across these per-fork
means: iterations within a fork share JIT/GC state and are autocorrelated, so
the fork is the independent unit. Produces a LaTeX table with absolute times
and deltas (written to the paper directory) plus the same table on stdout for
quick inspection.
"""

import argparse
import json
import math
import statistics
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

DEFAULT_RESULTS_DIR = Path(__file__).parent / "results"
SOURCES_DIR = Path(__file__).parent / "sources"
DEFAULT_OUTPUT = Path(__file__).parent / ".." / "paper" / "bench_table.tex"

# Suite class name -> column mapping
SUITES = {
    "FirstClassBaseBenchmarks": "first_class_base",
    "FirstClassBenchmarks": "first_class",
    "SchmidBaseBenchmarks": "schmid_base",
    "SchmidRefinementBenchmarks": "schmid",
    "StainlessBaseBenchmarks": "stainless_base",
    "StainlessVerifyBenchmarks": "stainless",
}

COLUMN_LABELS = {
    "first_class_base": "Base 3.8",
    "first_class": "First-class",
    "schmid_base": "Base 0.1",
    "schmid": "Schmid",
    "stainless_base": "Base (no plugin)",
    "stainless": "Stainless",
}

COLUMNS = [
    "first_class_base", "first_class",
    "schmid_base", "schmid",
    "stainless_base", "stainless",
]

# Platform groups: (label, base column, checked column)
PLATFORMS = [
    ("First-class", "first_class_base", "first_class"),
    ("Schmid", "schmid_base", "schmid"),
    ("Stainless", "stainless_base", "stainless"),
]

# Checked column -> source file suffix in sources/<bench>-<suffix>.scala
SOURCE_SUFFIX = {
    "first_class": "first-class",
    "schmid": "schmid",
    "stainless": "stainless",
}

# Delta columns for the stdout table: (column, base column)
DELTA_COLUMNS = [(checked, base) for _, base, checked in PLATFORMS]

# Two-sided 95% Student's t critical values by degrees of freedom.
T_95 = {
    1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571, 6: 2.447, 7: 2.365,
    8: 2.306, 9: 2.262, 10: 2.228, 11: 2.201, 12: 2.179, 13: 2.160,
    14: 2.145, 15: 2.131, 16: 2.120, 17: 2.110, 18: 2.101, 19: 2.093,
    20: 2.086, 25: 2.060, 30: 2.042,
}

# ---------------------------------------------------------------------------
# Parse JMH results
# ---------------------------------------------------------------------------

def parse_results(path, samples):
    """Accumulate per-fork mean times from one results file into
    {(column, bench): [fork_mean_ms, ...]}."""
    with open(path) as f:
        try:
            data = json.load(f)
        except json.JSONDecodeError:
            print(f"warning: skipping invalid or incomplete results file: {path}",
                  file=sys.stderr)
            return
    for entry in data:
        parts = entry["benchmark"].split(".")  # e.g. "bench.FirstClassBenchmarks.fibMemo"
        col = SUITES.get(parts[-2])
        if col is None:
            continue
        bench = parts[-1]
        for fork in entry["primaryMetric"]["rawData"]:
            if fork:
                samples.setdefault((col, bench), []).append(statistics.mean(fork))


def confidence95(raw):
    """95% confidence interval half-width for a list of per-fork means."""
    n = len(raw)
    if n < 2:
        return 0.0
    df = n - 1
    t = T_95.get(df, 1.96 if df > 30 else T_95[max(k for k in T_95 if k <= df)])
    return t * statistics.stdev(raw) / math.sqrt(n)


def load_all(results_dir):
    """Load results from all runs, return {(column, bench): {score, error, n}}
    where score is the mean of the per-fork means, error the 95% confidence
    interval half-width across forks, and n the number of forks."""
    samples = {}
    for path in sorted(results_dir.glob("*/*.json")):
        parse_results(path, samples)
    return {
        key: {"score": statistics.mean(means), "error": confidence95(means), "n": len(means)}
        for key, means in samples.items()
    }


def count_loc(bench, col):
    """Count source lines in the checked benchmark file, skipping blank lines
    and comment-only lines (`//` and leading `/* ... */` blocks)."""
    path = SOURCES_DIR / f"{bench}-{SOURCE_SUFFIX[col]}.scala"
    if not path.exists():
        return None
    count = 0
    in_block = False
    for line in open(path):
        s = line.strip()
        if in_block:
            if "*/" not in s:
                continue
            s = s.split("*/", 1)[1].strip()
            in_block = False
        while s.startswith("/*"):
            if "*/" in s:
                s = s.split("*/", 1)[1].strip()
            else:
                in_block = True
                s = ""
        if s and not s.startswith("//"):
            count += 1
    return count


def abs_overhead(b, c):
    """Absolute overhead (ms) of checked c over base b, with a 95% CI
    half-width combining the two intervals in quadrature."""
    return c["score"] - b["score"], math.sqrt(b["error"] ** 2 + c["error"] ** 2)


def pct_overhead(b, c):
    """Relative overhead (%) of checked c over base b, with a 95% CI
    half-width propagated from the two intervals (delta method on the
    ratio of independent means)."""
    ratio = c["score"] / b["score"]
    pct = (ratio - 1) * 100
    err = 100 * ratio * math.sqrt(
        (c["error"] / c["score"]) ** 2 + (b["error"] / b["score"]) ** 2
    )
    return pct, err


def build_table(results):
    """Build a table {bench: {col: {score, error, n}}} for all benchmarks
    that appear in at least one checked suite."""
    checked = {col for _, _, col in PLATFORMS}
    benches = sorted({bench for (col, bench) in results if col in checked})
    table = {}
    for bench in benches:
        table[bench] = {
            col: results[(col, bench)] for col in COLUMNS if (col, bench) in results
        }
    return table

# ---------------------------------------------------------------------------
# LaTeX table
# ---------------------------------------------------------------------------

def generate_latex_table(table):
    lines = []
    lines.append(r"\begin{figure*}[t]")
    lines.append(r"\centering")
    lines.append(r"\captionsetup{font=small}")
    lines.append(r"\footnotesize")
    lines.append(r"\begin{tabular}{l" + " rrr" * len(PLATFORMS) + "}")
    lines.append(r"\toprule")

    # Top header: platform names spanning 3 columns each
    top_header = ""
    for label, _, _ in PLATFORMS:
        top_header += f" & \\multicolumn{{3}}{{c}}{{{label}}}"
    top_header += r" \\"
    # cmidrules under each platform
    cmidrules = ""
    for i in range(len(PLATFORMS)):
        start = 2 + i * 3
        end = start + 2
        cmidrules += f"\\cmidrule(lr){{{start}-{end}}} "
    lines.append(top_header)
    lines.append(cmidrules)

    # Sub-header
    sub_header = "Benchmark"
    for _ in PLATFORMS:
        sub_header += r" & LoC & Base (ms) & $\Delta$ (ms)"
    sub_header += r" \\"
    lines.append(sub_header)
    lines.append(r"\midrule")

    for bench in sorted(table.keys()):
        row = r"\texttt{" + bench.replace("_", r"\_") + "}"
        for _, base_col, checked_col in PLATFORMS:
            has_base = base_col in table[bench]
            has_checked = checked_col in table[bench]
            # LoC: only for benchmarks that actually run on this platform (the
            # source file may exist without a benchmark, e.g. mergeSort-schmid
            # crashes the LiquidTyper and is commented out).
            loc = count_loc(bench, checked_col) if (has_base or has_checked) else None
            row += f" & ${loc}$" if loc else " & ---"
            # Unchecked
            if has_base:
                b = table[bench][base_col]
                row += f" & ${b['score']:.0f} \\pm {b['error']:.0f}$"
            else:
                row += " & ---"
            # Relative diff (the checked time itself is base * (1 + delta))
            if has_base and has_checked:
                b = table[bench][base_col]
                c = table[bench][checked_col]
                delta, delta_err = abs_overhead(b, c)
                row += f" & ${delta:.0f} \\pm {delta_err:.0f}$"
            else:
                row += " & ---"
        row += r" \\"
        lines.append(row)

    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\caption{Compilation time benchmarks (ms/op, single-shot). Each run (JMH fork) is reduced to its mean; scores are the mean of the per-run means $\pm$ the 95\% confidence interval across runs (Student's $t$). Each platform shows the unchecked baseline time and the absolute overhead of checking; the checked time is $\text{base} + \Delta$. The overhead interval combines the base and checked intervals in quadrature.}")
    lines.append(r"\label{fig:bench-table}")
    lines.append(r"\end{figure*}")
    return "\n".join(lines)

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def print_stdout_table(table):
    print("=" * 120)
    header = f"{'Benchmark':<18}"
    for col in COLUMNS:
        header += f"  {COLUMN_LABELS[col]:>21}"
    print(header)
    print("-" * 120)
    for bench in sorted(table.keys()):
        row = f"{bench:<18}"
        for col in COLUMNS:
            if col in table[bench]:
                d = table[bench][col]
                cell = f"{d['score']:.0f}±{d['error']:.0f}"
                for dcol, bcol in DELTA_COLUMNS:
                    if col == dcol and bcol in table[bench]:
                        b = table[bench][bcol]
                        delta = d["score"] - b["score"]
                        pct, pct_err = pct_overhead(b, d)
                        sign = "+" if delta >= 0 else ""
                        cell += f" ({sign}{delta:.0f}, {sign}{pct:.0f}±{pct_err:.0f}%)"
            else:
                cell = "---"
            row += f"  {cell:>21}"
        print(row)
    print("=" * 120)


def main():
    parser = argparse.ArgumentParser(description="Generate the benchmark results LaTeX table from JMH JSON results.")
    parser.add_argument("--results-dir", type=Path, default=DEFAULT_RESULTS_DIR,
                        help="directory containing <suite>/<run>.json files (default: results/)")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT,
                        help="output .tex path (default: ../paper/bench_table.tex)")
    args = parser.parse_args()

    results = load_all(args.results_dir)
    if not results:
        parser.error(f"no results found in {args.results_dir}")
    table = build_table(results)

    print(f"Benchmarks included: {sorted(table.keys())}")
    print()

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with open(args.output, "w") as f:
        f.write(generate_latex_table(table))
    print(f"Written {args.output}")

    print()
    print_stdout_table(table)


if __name__ == "__main__":
    main()
