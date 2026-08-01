# Evaluation

Compilation-time benchmarks comparing three refinement-type checkers for
Scala, each against an unchecked baseline compiled by the same compiler:

| Suite | Checked configuration | Baseline |
|-------|-----------------------|----------|
| [first-class/](first-class/) | Our qualified-types Scala 3 fork with `-language:experimental.qualifiedTypes` | Same programs without refinement annotations |
| [stainless/](stainless/) | Stainless run as a Dotty compiler plugin (verification on, native Z3) | Contract-free sources, same Dotty without the plugin |
| [schmid/](schmid/) | Georg Schmid's 2016 LiquidTyper extension to Dotty 0.1 | Same programs without refinements, LiquidTyper skipped |

See the per-suite READMEs for prerequisites, native (non-Docker) setup, and
how to run individual benchmarks.

## Layout

- [`sources/`](./sources/): the benchmark programs, shared by all suites. One file per
  benchmark and platform variant: `<bench>-<platform>.scala` (checked) and
  `<bench>-<platform>-base.scala` (baseline), e.g. `intarray-first-class.scala`,
  `intarray-stainless-base.scala`. Not every benchmark exists on every
  platform (LiquidTyper and Stainless support a subset of the programs).
- [`first-class/`](./first-class/), [`stainless/`](./stainless/), [`schmid/`](./schmid/): one sbt project per suite, each
  with a JMH harness (`bench/`) that invokes the corresponding compiler
  programmatically on the sources.
- [`run.sh`](./run.sh): the benchmark runner (see below).
- [`make_table.py`](./make_table.py): generates the paper's results table (see below).
- [`results-laraserver4-2/`](./results-laraserver4-2/): the paper's results, collected on a dedicated
  x86-64 Linux server.

## Running benchmarks (`run.sh`)

```sh
./run.sh --suite first-class|stainless|schmid|all [--dry-run | --runs N] [--results-dir DIR]
```

- `--dry-run` runs each benchmark once with no warmup — quick sanity check
  only, the timings are meaningless.
- The full configuration (the default) runs 150 warmup + 20 measurement
  iterations per benchmark, in one forked JVM per benchmark.
- `--runs N` repeats the whole selection N times with runs as the outer
  loop, so suites are interleaved (this spreads slow drift of the machine's
  performance evenly across suites).

JMH results are written to `<results-dir>/<suite>/<run>.json` (default
results dir: `results/`), where `<run>` is the date and time the suite's run
started, e.g. `2026-07-20-1633.json`, with a `-dry` suffix for dry runs.
Results from separate invocations accumulate side by side, and
`make_table.py` pools all of them.

In the artifact image, the same runner is invoked through the entry point:

```sh
docker run --platform linux/amd64 -v "$PWD/results:/work/evaluation/results" \
  refinement-artifact evaluation bench --suite all --dry-run
```

## Generating the results table (`make_table.py`)

```sh
python3 make_table.py [--results-dir DIR] [--output FILE]
```

Reads every `<results-dir>/<suite>/<run>.json` file (default:
`results-laraserver4-2/`, the paper's results — so running it with no
arguments reproduces the paper's table), writes the LaTeX table to stdout
(or to `--output FILE`), and prints a human-readable version with
additional relative-overhead columns to stderr. Files that do not parse
(e.g. a run still in progress) are skipped with a warning.

### How the values are computed

JMH measures single-shot compilation time (ms). Iterations within one fork
(one JVM invocation) share JIT and GC state and are therefore
autocorrelated, so the fork — not the iteration — is treated as the
independent unit of measurement:

1. **Per-fork mean.** Each fork $f$ is reduced to the mean of its
   measurement iterations, $x_f$. With the paper's configuration there is
   one fork per benchmark per run file, so pooling all run files gives one
   sample $x_f$ per run, $n$ samples in total.

2. **Score.** The reported time for a benchmark/configuration is the mean of
   the per-fork means:

$$\bar{x} = \frac{1}{n} \sum_{f=1}^{n} x_f$$

3. **Confidence interval.** The reported error is the half-width of the 95%
   confidence interval across forks, using Student's $t$ distribution with
   $n - 1$ degrees of freedom ($s$ is the sample standard deviation of the
   $x_f$):

$$e = t_{0.975,\,n-1} \cdot \frac{s}{\sqrt{n}}$$

4. **Checking overhead (LaTeX table).** For each platform the table shows
   the baseline time $\bar{x}_b \pm e_b$ and the absolute overhead of
   checking $\Delta = \bar{x}_c - \bar{x}_b$ (the checked time is
   $\bar{x}_b + \Delta$). Since baseline and checked samples are
   independent, their interval half-widths combine in quadrature:

$$e_\Delta = \sqrt{e_b^2 + e_c^2}$$

5. **Relative overhead (console table only).** The percentage overhead is
   $\delta = (r - 1) \cdot 100$ with $r = \bar{x}_c / \bar{x}_b$, and its
   interval is propagated by the delta method for a ratio of independent
   means:

$$e_\delta = 100 \, r \sqrt{\left(\frac{e_c}{\bar{x}_c}\right)^2 + \left(\frac{e_b}{\bar{x}_b}\right)^2}$$

6. **Lines of code.** The LoC column counts source lines of the checked
   variant (`sources/<bench>-<platform>.scala`), skipping blank lines and
   comment-only lines.
