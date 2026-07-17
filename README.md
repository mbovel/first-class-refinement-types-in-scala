# First-Class Refinement Types in Scala — Artifact

This artifact contains the compilation-time benchmarks comparing our
first-class refinement types implementation with Stainless and with Georg
Schmid's 2016 LiquidTyper ([evaluation/](evaluation/)), and the Coq
mechanization ([mechanization/](mechanization/)).

**We recommend running the benchmarks with the prebuilt Docker image
(`evaluation-image.tar`, included in the artifact archive) — no build step is
required.** The image contains all toolchains (JDK 25, JDK 8, sbt, Z3), the
prebuilt compilers, and cached dependencies, so it runs without network
access.

## Requirements

- Docker, with ≥ 10 GB of memory available to containers (the benchmark JVMs
  use 8 GB heaps)
- x86-64 image: on Apple Silicon, pass `--platform linux/amd64` (Docker
  Desktop runs it under Rosetta); on x86-64 Linux the flag is a no-op
- ~6 GB of disk for the loaded image

## Getting started (~15 minutes)

Load the image (~2 min):

```sh
docker load -i evaluation-image.tar
```

Run all three benchmark suites once, without warmup, collecting results into
`./results/` (~10 min):

```sh
mkdir -p results
docker run --platform linux/amd64 -v "$PWD/results:/work/evaluation/results" \
  refinement-bench --suite all --dry-run
```

This should produce `results/0/first-class.json`, `results/0/stainless.json`,
and `results/0/schmid.json` (JMH result files, one entry per benchmark; a dry
run writes to run directory `0`, full runs to `1..N`).

## Full benchmark runs

Full runs use the paper's JMH configuration (150 warmup + 20 measurement
iterations per benchmark) and take **several hours per suite**; add
`--runs N` to repeat the whole selection N times (suites interleaved,
results in `results/1..N/`):

```sh
docker run --platform linux/amd64 -v "$PWD/results:/work/evaluation/results" \
  refinement-bench --suite first-class
docker run --platform linux/amd64 -v "$PWD/results:/work/evaluation/results" \
  refinement-bench --suite stainless
docker run --platform linux/amd64 -v "$PWD/results:/work/evaluation/results" \
  refinement-bench --suite schmid
```

For an interactive shell inside the image (e.g. to run a single benchmark;
see the per-suite READMEs under [evaluation/](evaluation/)):

```sh
docker run --platform linux/amd64 --entrypoint bash -it refinement-bench
```

## Building from source (optional — not needed for evaluation)

The image can be rebuilt from this repository with
`docker build --platform linux/amd64 -t refinement-bench evaluation`
(~20 min, network required), and the suites can also be run natively without
Docker (see [evaluation/first-class/README.md](evaluation/first-class/README.md),
[evaluation/stainless/README.md](evaluation/stainless/README.md), and
[evaluation/schmid/README.md](evaluation/schmid/README.md); the Stainless and
refined-dotty compilers are built by the respective `setup.sh` scripts).
Note that the from-source path depends on external package repositories,
including legacy ones for the 2016 LiquidTyper toolchain — the prebuilt
image is the reproducible path.

## Contents

- `evaluation-image.tar` — prebuilt Docker image (artifact archive only)
- `VERSION` — git commit this artifact was built from (artifact archive only)
- `evaluation/` — benchmark suites, sources, runner, and Dockerfile
- `mechanization/` — Coq mechanization
