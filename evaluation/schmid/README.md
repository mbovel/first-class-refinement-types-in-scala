# Georg Schmid's LiquidTyper Evaluation

Compilation-time benchmarks for Georg Schmid's 2016 LiquidTyper extension to Dotty, using his original 10 benchmark programs.

## Prerequisites

- JDK 8 (required by sbt 0.13 used in the old Dotty fork)
- Z3 (`brew install z3` or equivalent)
- sbt

## Setup

### 1. Switch to JDK 8

```sh
eval $(cs java --jvm 8 --env)
```

### 2. Publish Georg's Dotty fork locally

The `related-work/schmid2016/artifact` submodule points to `mbovel/dotty@liquidtyper-fix`, a fork of Georg's Dotty with build fixes and suppressed debug output.

```sh
cd related-work/schmid2016/artifact
eval $(cs java --jvm 8 --env) && sbt publishLocal
```

This publishes `ch.epfl.lamp:dotty_2.11:0.1-SNAPSHOT` to the local Ivy cache.

### 3. Switch back to JDK 25

```sh
eval $(cs java --jvm 25 --env)
```

The benchmarks run in a JMH-forked JVM using JDK 8 (configured via sbt).

**Note**: sbt in `evaluation/schmid/` must be run with a JDK that supports sbt 1.x (JDK 11+), but the JMH forked JVM will use whatever `java` is on `PATH`. The Georg compiler itself only requires JDK 8 classes, which are available on newer JDKs.

## Running benchmarks

All commands are run from the `evaluation/schmid/` directory.

### Quick test (single iteration, no warmup)

```sh
sbt 'Jmh / run -wi 0 -i 1 SchmidRefinementBenchmarks'
```

### Single benchmark

```sh
sbt 'Jmh / run -wi 0 -i 1 SchmidRefinementBenchmarks.rational'
```

### Full run (150 warmup, 20 measurement iterations)

```sh
sbt 'Jmh / run SchmidRefinementBenchmarks'
```

## Benchmark sources

Source files are in the shared `../sources/` directory, using Georg's `{ v: Type if predicate }` syntax (`*-schmid.scala`) or without refinements (`*-schmid-base.scala`, compiled with `-Yskip:liquidtyper` by `SchmidBaseBenchmarks`):

| Benchmark | Description |
|-----------|-------------|
| `max-schmid.scala` | `max` with full postcondition `v >= x && v >= y && (v == x \|\| v == y)` |
| `sumnat-schmid.scala` | Recursive `sumNat` with `NonNeg` type, `safeAdd` |
| `intarray-schmid.scala` | Array with bounds-checked `access` method |
| `postuple-schmid.scala` | Tuple with `a + b > 0` constraint |
| `list1-schmid.scala` | `List[NonNeg]` with `.head` preserving refinement |
| `list2-schmid.scala` | `List[NonNeg]` with `.reverse` preserving type parameter |
| `hofsafety1-schmid.scala` | HOF `g(f: NonNeg => Int)` called with refined lambda |
| `hofsafety2-schmid.scala` | Closure returning `NonNeg => NonNeg` |
| `arrfold-schmid.scala` | Generic `arrFold[A]` with `arrSum` and `arrMax` |
| `rational-schmid.scala` | `Rational` class with `q != 0` constraint |

These are the exact programs from Georg's test suite (`LiquidTyperTests.scala`).

## Dependencies

- `ch.epfl.lamp:dotty_2.11:0.1-SNAPSHOT` (published locally from Georg's fork)
- `leon_2.11-3.0.jar`, `scala-smtlib_2.11.jar` (in `lib/`, provide Z3 SMT-LIB interface)
- `interface-0.13.11.jar` (in `lib/`, sbt interface for old Dotty)

## Georg's Dotty fork modifications

The fork at `mbovel/dotty@liquidtyper-fix` includes:

1. Build fixes for compatibility with modern sbt/JDK
2. Suppressed LiquidTyper debug output (`ltypr` printer set to `noPrinter`, `ctx.echo` calls commented out)
