# First-Class Refinement Types in Scala — Artifact

> [!IMPORTANT]
> **Reviewer's guide:** evaluating this artifact only requires
> [Getting started](#getting-started-20-minutes) (checks all three components,
> ~20 min) and [Regenerating the results table](#regenerating-the-results-table)
> (reproduces the paper's table from the shipped results), plus optionally
> [Compiling a program with refinement
> types](#compiling-a-program-with-refinement-types-optional) to try the
> compiler on examples. The remaining sections (full benchmark runs, re-building
> the image, running natively, packaging) are documented for completeness and
> reusability; running them is not expected.

This repository is the artifact for the paper *First-Class Refinement Types
in Scala*. It contains:

- [implementation/](implementation/): our fork of the Scala 3 compiler
  implementing first-class refinement types (called *qualified types* in the
  implementation, enabled by `-language:experimental.qualifiedTypes`). The
  implementation is self-contained in the
  [qualified_types](https://github.com/mbovel/dotty/tree/7ffb8c7a3b292d109a6cad868bbdb1455c99f727/compiler/src/dotty/tools/dotc/qualified_types)
  package; see [its README](https://github.com/mbovel/dotty/blob/7ffb8c7a3b292d109a6cad868bbdb1455c99f727/compiler/src/dotty/tools/dotc/qualified_types/README.md)
  for an overview and how to run the compiler and its test suites. PR: [scala/scala3#21586](https://github.com/scala/scala3/pull/21586).
- [mechanization/](mechanization/): the Rocq mechanization (see
  [mechanization/README.md](mechanization/README.md), or browse the proofs in
  the [rendered Rocq doc](https://mbovel.github.io/first-class-refinement-types-in-scala/mechanization/toc.html)).
- [evaluation/](evaluation/): compilation-time benchmarks comparing our
  implementation with Stainless and with [Georg Schmid's 2016
  LiquidTyper](https://dl.acm.org/doi/10.1145/2998392.2998398), plus the script
  that generates the paper's results table (see
  [evaluation/README.md](evaluation/README.md)).
- [paper/](paper/): the paper's LaTeX sources, including the generated
  benchmark table (`bench_table.tex`).

## Requirements

- Docker, with ≥ 10 GB of memory available to containers (the benchmark JVMs
  use 8 GB heaps)
- x86-64 image: on Apple Silicon, pass `--platform linux/amd64` (Docker
  Desktop runs it under Rosetta); on x86-64 Linux the flag is a no-op
- ~8 GB of disk for the loaded image

## Getting started (~20 minutes)

Load the image (~2 min):

```sh
docker load -i artifact-image.tar
```

Then run the image with no arguments:

```sh
docker run --rm --platform linux/amd64 refinement-artifact
```

This exercises all three executable components once, announcing each stage with
a banner:

- 📜 **[1/3] Mechanization**: compiles all Rocq proofs (success means every
  theorem is machine-checked)
- 🛠️ **[2/3] Implementation**: compiles an example program
  ([list_collect.scala](implementation/tests/pos-custom-args/qualified-types/list_collect.scala))
  with the qualified-types compiler
- ⏱️ **[3/3] Evaluation**: runs all three benchmark suites once, without
  warmup (a "dry run"), to check that they work end to end

A final `✅ Done` banner confirms all three stages succeeded.

> [!NOTE]
> On Apple Silicon under Rosetta, a race condition in the benchmark framework
> can hang the run at `[info] running (fork)
> org.openjdk.jmh.generators.bytecode.JmhBytecodeGenerator`. If this happens,
> kill the container and rerun the command.

## Regenerating the results table

`evaluation make-table` renders the paper's benchmark table from JMH result
files: the LaTeX table goes to stdout (redirect it to a file), and a
human-readable version with relative-overhead columns is printed to stderr.
By default it reads the paper's own results, recorded in
[evaluation/results-laraserver4/](evaluation/results-laraserver4/) and
shipped in the image — so this reproduces the paper's table exactly, with
no volume mounts needed:

```sh
docker run --rm --platform linux/amd64 refinement-artifact \
  evaluation make-table > paper/bench_table.tex
```

How the scores, confidence intervals, and overhead columns are computed is
documented in [evaluation/README.md](evaluation/README.md).

## Compiling a program with refinement types (optional)

The `implementation` command forwards its arguments to sbt in the compiler
checkout, where the `scala3-nonbootstrapped / scalac` task invokes the
qualified-types compiler. To compile one of the bundled examples:

```sh
docker run --rm --platform linux/amd64 refinement-artifact implementation \
  "scala3-nonbootstrapped / scalac -language:experimental.qualifiedTypes tests/pos-custom-args/qualified-types/list_collect.scala"
```

Relative paths are resolved from `implementation/`; see
[tests/pos-custom-args/qualified-types/](implementation/tests/pos-custom-args/qualified-types/)
for more examples.

## Full benchmark runs (optional, ⚠️ several hours to days)

Full runs use the paper's JMH configuration: 150 warmup + 20 measurement
iterations per benchmark, one fork per benchmark per run. One full pass over
all three suites takes **~3 hours on a fast x86-64 server**, and the paper's
numbers aggregate `--runs 10` such passes (30+ hours total).

If you do want to run them, results accumulate under the mounted `results/`
directory, one timestamped file per suite per run:

```sh
mkdir results
chmod 777 results
docker run --rm --platform linux/amd64 -v "$PWD/results:/work/evaluation/results" \
  refinement-artifact evaluation bench --suite all --runs 10
```

> [!NOTE]
> The `chmod` lets the container's non-root user write into the host-created
> directory; in the other direction, the container creates its output
> world-writable, so the result files can be moved or deleted on the host
> without sudo. This matters wherever bind mounts expose raw file ownership
> (native Linux, and some macOS/Windows runtimes); Docker Desktop remaps
> ownership to the host user by itself, making both steps harmless no-ops.

Once runs have completed, render the table from your own results instead of
the shipped ones by mounting them read-only and pointing `--results-dir` at
them:

```sh
docker run --rm --platform linux/amd64 -v "$PWD/results:/work/evaluation/results:ro" \
  refinement-artifact evaluation make-table --results-dir evaluation/results > paper/bench_table.tex
```

## Re-building the Docker image (optional)

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

The build compiles all three compilers inside the image (the Stainless and
refined-dotty ones via their `setup.sh` scripts, see below). Note that it
depends on external package repositories, including legacy ones for the 2016
LiquidTyper toolchain; the prebuilt image is the reproducible path.

## Running natively (optional)

The mechanization and the suites can also be run without Docker (see
[mechanization/README.md](mechanization/README.md),
[evaluation/first-class/README.md](evaluation/first-class/README.md),
[evaluation/stainless/README.md](evaluation/stainless/README.md), and
[evaluation/schmid/README.md](evaluation/schmid/README.md)). For the
Stainless and schmid suites, first build their compilers with the setup
scripts shown in the next section.

## Packaging the artifact (optional)

[package.sh](package.sh) assembles the archive uploaded to Zenodo: this
repository (without `.git` and build residue) plus the saved Docker image,
as a single zip. It requires the image to be built (see "Re-building the
Docker image") and both compiler `lib/` directories to be populated by the
setup scripts (each initializes its submodule if needed), so that the
shipped source tree is usable on its own:

```sh
./evaluation/stainless/setup.sh  # builds the Stainless jars into evaluation/stainless/lib
./evaluation/schmid/setup.sh     # builds the refined-dotty jars into evaluation/schmid/lib
./package.sh                     # writes artifact/first-class-refinement-types.zip
```

The schmid script needs JDK 8, either on `PATH`, via `JDK8_HOME`, or fetched
automatically through [coursier](https://get-coursier.io) (`cs`) if installed.

## Contents

- `artifact-image.tar`: prebuilt Docker image (artifact archive only)
- `VERSION`: git commit this artifact was built from (artifact archive only)
- `run.sh`: entry point (used by the image; also runnable from a checkout)
- `implementation/`: qualified-types Scala 3 compiler fork
- `mechanization/`: Rocq mechanization
- `evaluation/`: benchmark suites, sources, runner, and table generator
- `paper/`: paper LaTeX sources
- `Dockerfile`: builds the artifact image
- `package.sh`: assembles the artifact archive (repository + saved image)
