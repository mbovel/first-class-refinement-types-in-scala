# First-Class Refinement Types in Scala — Artifact

This repository is the artifact for the paper *First-Class Refinement Types
in Scala*. It contains:

- [implementation/](implementation/): our fork of the Scala 3 compiler
  implementing first-class refinement types (called *qualified types* in the
  implementation, enabled by `-language:experimental.qualifiedTypes`). The
  implementation is self-contained in the
  [qualified_types](https://github.com/mbovel/dotty/tree/7ffb8c7a3b292d109a6cad868bbdb1455c99f727/compiler/src/dotty/tools/dotc/qualified_types)
  package; see [its README](https://github.com/mbovel/dotty/blob/7ffb8c7a3b292d109a6cad868bbdb1455c99f727/compiler/src/dotty/tools/dotc/qualified_types/README.md)
  for an overview and how to run the compiler and its test suites.
- [mechanization/](mechanization/): the Rocq mechanization: System F
  with refinement and dependent function types, formalized with a
  definitional interpreter and semantic types
  (see [mechanization/README.md](mechanization/README.md)).
- [evaluation/](evaluation/): compilation-time benchmarks comparing our
  implementation with Stainless and with [Georg Schmid's 2016
  LiquidTyper](https://dl.acm.org/doi/10.1145/2998392.2998398), plus the script
  that generates the paper's results table (see
  [evaluation/README.md](evaluation/README.md)).
- [paper/](paper/): the paper's LaTeX sources, including the generated
  benchmark table (`bench_table.tex`).

**We recommend using the prebuilt Docker image (`artifact-image.tar`, included
in the artifact archive).** Using the image, no build step is required. The
image contains all toolchains (Rocq 9.2, JDK 25, JDK 8, sbt, Z3), the prebuilt
compilers, and cached dependencies, so it runs without network access.

## Requirements

- Docker, with ≥ 10 GB of memory available to containers (the benchmark JVMs
  use 8 GB heaps)
- x86-64 image: on Apple Silicon, pass `--platform linux/amd64` (Docker
  Desktop runs it under Rosetta); on x86-64 Linux the flag is a no-op
- ~6 GB of disk for the loaded image

## Getting started (~20 minutes)

Load the image (~2 min):

```sh
docker load -i artifact-image.tar
```

Then run the image with no arguments:

```sh
docker run --platform linux/amd64 refinement-artifact
```

This exercises all three executable components once, announcing each stage with
a banner:

- 📜 **[1/3] Mechanization** — compiles all Rocq proofs (success means every
  theorem is machine-checked)
- 🛠️ **[2/3] Implementation** — compiles an example program
  ([list_collect.scala](implementation/tests/pos-custom-args/qualified-types/list_collect.scala))
  with the qualified-types compiler
- ⏱️ **[3/3] Evaluation** — runs all three benchmark suites once, without
  warmup (a "dry run"), to check that they work end to end

A final `✅ Done` banner confirms all three stages succeeded.

## Full benchmark runs (⚠️ several hours to days)

Full runs use the paper's JMH configuration: 180 warmup + 40 measurement
iterations per benchmark, one fork per benchmark per run. One full pass over
all three suites takes **~3 hours on a fast x86-64 server**, and the paper's
numbers aggregate `--runs 10` such passes (30+ hours total).

If you do want to run them, results accumulate under the mounted `results/`
directory, one timestamped file per suite per run:

```sh
mkdir results
chmod +777 results
docker run --platform linux/amd64 -v "$PWD/results:/work/evaluation/results" \
  refinement-artifact evaluation bench --suite all --runs 10
```

## Regenerating the results table

`evaluation make-table` renders the paper's benchmark table (LaTeX, plus a
console version on stdout) from JMH result files. By default it reads the
paper's own results, recorded in
[evaluation/results-laraserver4/](evaluation/results-laraserver4/) and
shipped in the image — so this reproduces the paper's table exactly. Mount a
`paper/` directory so the generated `bench_table.tex` is written to the
host:

```sh
docker run --platform linux/amd64 -v "$PWD/paper:/work/paper" \
  refinement-artifact evaluation make-table
```

To build the table from results you collected yourself instead, mount them
too and point `--results-dir` at them:

```sh
docker run --platform linux/amd64 \
  -v "$PWD/paper:/work/paper" -v "$PWD/results:/work/evaluation/results" \
  refinement-artifact evaluation make-table --results-dir evaluation/results
```

How the scores, confidence intervals, and overhead columns are computed is
documented in [evaluation/README.md](evaluation/README.md).

## Building from source (optional, not needed for evaluation)

The image can be rebuilt from this repository. First initialize the
compiler submodules (`implementation` deliberately without `--recursive`:
its community-build submodules are large and not needed):

```sh
git submodule update --init implementation
git submodule update --init --recursive evaluation/stainless/stainless
git submodule update --init evaluation/schmid/refined-dotty
```

Then build from the repository root (~20 min, network required):

```sh
docker build --platform linux/amd64 -t refinement-artifact .
```

The mechanization and the suites can also be run natively without Docker
(see [mechanization/README.md](mechanization/README.md),
[evaluation/first-class/README.md](evaluation/first-class/README.md),
[evaluation/stainless/README.md](evaluation/stainless/README.md), and
[evaluation/schmid/README.md](evaluation/schmid/README.md); the Stainless and
refined-dotty compilers are built by the respective `setup.sh` scripts).
Note that the from-source path depends on external package repositories,
including legacy ones for the 2016 LiquidTyper toolchain — the prebuilt
image is the reproducible path.

## Contents

- `artifact-image.tar` — prebuilt Docker image (artifact archive only)
- `VERSION` — git commit this artifact was built from (artifact archive only)
- `run.sh` — entry point (used by the image; also runnable from a checkout)
- `implementation/` — qualified-types Scala 3 compiler fork
- `mechanization/` — Rocq mechanization
- `evaluation/` — benchmark suites, sources, runner, and table generator
- `paper/` — paper LaTeX sources
- `Dockerfile` — builds the artifact image
