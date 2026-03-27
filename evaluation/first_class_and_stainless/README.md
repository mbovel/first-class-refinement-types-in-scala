# Evaluation

Compilation-time benchmarks comparing four configurations of refinement types in Scala:

- **First-class** (`RefinementsFirstClassBenchmarks`): our qualified types extension to Scala 3, using the `ch.epfl.lara` Dotty fork with `-language:experimental.qualifiedTypes`.
- **Base** (`RefinementsBaseBenchmarks`): same programs without refinement type annotations, as a baseline.
- **Stainless verify** (`StainlessVerifyBenchmarks`): Stainless extraction and verification via compiler plugin (`-P:stainless:verify:yes`), using native Z3.
- **Stainless no-verify** (`StainlessNoVerifyBenchmarks`): Stainless extraction only, no verification (`-P:stainless:verify:no`).

## Prerequisites

- JDK 25 (for first-class and Stainless benchmarks)
- Z3 (`brew install z3` or equivalent)
- sbt

## Setup

From the `evaluation/first_class_and_stainless/` directory:

```sh
./setup.sh
```

This initializes the `stainless` submodule (a fork with benchmark-specific changes), builds the Stainless assembly and library jars, and copies them to `lib/`.

## Running benchmarks

All commands are run from the `evaluation/first_class_and_stainless/` directory.

### Quick test (single iteration, no warmup)

```sh
# First-class refinement types
sbt 'bench / Jmh / run -wi 0 -i 1 RefinementsFirstClassBenchmarks'

# Base (no refinements)
sbt 'bench / Jmh / run -wi 0 -i 1 RefinementsBaseBenchmarks'

# Stainless with verification
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessVerifyBenchmarks'

# Stainless extraction only (no verification)
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessNoVerifyBenchmarks'
```

### Single benchmark

```sh
sbt 'bench / Jmh / run -wi 0 -i 1 RefinementsFirstClassBenchmarks.postuple'
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessVerifyBenchmarks.matrixDims'
```

### Full run (150 warmup, 20 measurement iterations)

```sh
sbt 'bench / Jmh / run RefinementsFirstClassBenchmarks'
sbt 'bench / Jmh / run RefinementsBaseBenchmarks'
sbt 'bench / Jmh / run StainlessVerifyBenchmarks'
sbt 'bench / Jmh / run StainlessNoVerifyBenchmarks'
```

## Benchmark sources

Source files are in `bench-sources/`, organized by approach:

| Directory | Description |
|-----------|-------------|
| `bench-sources/first_class/` | First-class qualified types (`{v: T with p}`) |
| `bench-sources/base/` | Same programs, no refinements |
| `bench-sources/stainless/` | Stainless style (`require`/`ensuring`, `BigInt`) |

## Stainless plugin modifications

The Stainless fork (`mbovel/stainless@refinement-types-eval`) includes:

1. **ScalaZ3 bundled in assembly jar**: removed the `assemblyExcludedJars` filter for ScalaZ3 and added `.dylib` to native lib detection, so Z3 native libraries are included directly in the assembly jar.
2. **Verification failures as compilation errors**: when `report.isSuccess` is false, emits a Dotty `Diagnostic.Error("Stainless verification failed")` so benchmark harness detects failures.
3. **Suppressed non-error output**: INFO, DEBUG, WARNING, and progress messages from the Stainless reporter adapter are suppressed; only ERROR/FATAL/INTERNAL messages are forwarded to Dotty.
4. **`GhostAccessRewriter` compatibility**: added explicit `run` override for compatibility with the Dotty nightly.
5. **Scala nightly bump**: updated from `3.8.3-RC1` to `3.8.4-RC1-bin-20260316-3082482-NIGHTLY`.
6. **Inox submodule**: pointed to `mbovel/inox@refinement-types-eval` fork.
