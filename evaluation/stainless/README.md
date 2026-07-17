# Stainless Evaluation

Compilation-time benchmarks for Stainless, run as a Dotty compiler plugin:

- **Stainless verify** (`StainlessVerifyBenchmarks`): Stainless extraction and verification via compiler plugin (`-P:stainless:verify:yes`), using native Z3.
- **Stainless no-verify** (`StainlessNoVerifyBenchmarks`): Stainless extraction only, no verification (`-P:stainless:verify:no`).
- **Base** (`StainlessBaseBenchmarks`): same programs without contracts, compiled with plain Dotty (no plugin), as a baseline.

## Prerequisites

- JDK 25
- Z3 (`brew install z3` or equivalent)
- sbt

## Setup

From the `evaluation/stainless/` directory:

```sh
./setup.sh
```

This initializes the `stainless` submodule (a fork with benchmark-specific changes), builds the Stainless assembly and library jars, and copies them to `lib/`.

## Running benchmarks

All commands are run from the `evaluation/stainless/` directory.

### Quick test (single iteration, no warmup)

```sh
# Stainless with verification
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessVerifyBenchmarks'

# Stainless extraction only (no verification)
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessNoVerifyBenchmarks'

# Base (plain Dotty, no contracts)
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessBaseBenchmarks'
```

### Single benchmark

```sh
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessVerifyBenchmarks.matrixDims'
```

### Full run (150 warmup, 20 measurement iterations)

```sh
sbt 'bench / Jmh / run StainlessVerifyBenchmarks'
sbt 'bench / Jmh / run StainlessNoVerifyBenchmarks'
sbt 'bench / Jmh / run StainlessBaseBenchmarks'
```

## Benchmark sources

Source files are in the shared `../sources/` directory, distinguished by suffix:

| Suffix | Description |
|--------|-------------|
| `*-stainless.scala` | Stainless style (`require`/`ensuring`, `BigInt`) |
| `*-stainless-base.scala` | Same programs, no contracts, plain Scala |

## Stainless plugin modifications

The Stainless fork (`mbovel/stainless@refinement-types-eval`) includes:

1. **ScalaZ3 bundled in assembly jar**: removed the `assemblyExcludedJars` filter for ScalaZ3 and added `.dylib` to native lib detection, so Z3 native libraries are included directly in the assembly jar.
2. **Verification failures as compilation errors**: when `report.isSuccess` is false, emits a Dotty `Diagnostic.Error("Stainless verification failed")` so benchmark harness detects failures.
3. **Suppressed non-error output**: INFO, DEBUG, WARNING, and progress messages from the Stainless reporter adapter are suppressed; only ERROR/FATAL/INTERNAL messages are forwarded to Dotty.
4. **`GhostAccessRewriter` compatibility**: added explicit `run` override for compatibility with the Dotty nightly.
5. **Scala nightly bump**: updated from `3.8.3-RC1` to `3.8.4-RC1-bin-20260316-3082482-NIGHTLY`.
6. **Inox submodule**: pointed to `mbovel/inox@refinement-types-eval` fork.
