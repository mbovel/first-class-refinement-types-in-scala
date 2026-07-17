# First-Class Refinement Types Evaluation

Compilation-time benchmarks for our qualified types extension to Scala 3, using the `ch.epfl.lara` Dotty fork:

- **First-class** (`FirstClassBenchmarks`): with `-language:experimental.qualifiedTypes`.
- **Base** (`FirstClassBaseBenchmarks`): same programs without refinement type annotations, as a baseline.

## Prerequisites

- JDK 25
- sbt

## Running benchmarks

All commands are run from the `evaluation/first-class/` directory.

### Quick test (single iteration, no warmup)

```sh
# First-class refinement types
sbt 'bench / Jmh / run -wi 0 -i 1 FirstClassBenchmarks'

# Base (no refinements)
sbt 'bench / Jmh / run -wi 0 -i 1 FirstClassBaseBenchmarks'
```

### Single benchmark

```sh
sbt 'bench / Jmh / run -wi 0 -i 1 FirstClassBenchmarks.postuple'
```

### Full run (150 warmup, 20 measurement iterations)

```sh
sbt 'bench / Jmh / run FirstClassBenchmarks'
sbt 'bench / Jmh / run FirstClassBaseBenchmarks'
```

## Benchmark sources

Source files are in the shared `../sources/` directory, distinguished by suffix:

| Suffix | Description |
|--------|-------------|
| `*-first-class.scala` | First-class qualified types (`{v: T with p}`) |
| `*-first-class-base.scala` | Same programs, no refinements |
