# Georg Schmid's LiquidTyper Evaluation

Compilation-time benchmarks for Georg Schmid's 2016 LiquidTyper extension to Dotty, using his original 10 benchmark programs.

## Prerequisites

- JDK 8 (required by sbt 0.13 used in the old Dotty fork; installed automatically via coursier if `cs` is available)
- Z3 (`brew install z3` or equivalent)
- sbt

## Setup

From the `evaluation/schmid/` directory:

```sh
./setup.sh
```

This initializes the `refined-dotty` submodule (`mbovel/dotty@liquidtyper-fix`, a fork of Georg's Dotty with build fixes and suppressed debug output), builds it with JDK 8, and copies the resulting jars to `lib/` together with the Leon and scala-smtlib jars it vendors.

JDK 8 is located as follows: `$JDK8_HOME` if set, the current `java` if it is a JDK 8, or `cs java --jvm temurin:8` as a fallback.

## Running benchmarks

All commands are run from the `evaluation/schmid/` directory. sbt itself runs on a modern JDK (11+), but the JMH harness and the forked JVMs that run the Georg compiler use JDK 8, located automatically by `build.sbt` (`$JDK8_HOME` if set, otherwise `cs java-home --jvm temurin:8`).

### Quick test (single iteration, no warmup)

```sh
sbt 'bench / Jmh / run -wi 0 -i 1 SchmidRefinementBenchmarks'
```

### Single benchmark

```sh
sbt 'bench / Jmh / run -wi 0 -i 1 SchmidRefinementBenchmarks.rational'
```

### Full run (150 warmup, 20 measurement iterations)

```sh
sbt 'bench / Jmh / run SchmidRefinementBenchmarks'
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
| `hof1-schmid.scala` | HOF `g(f: NonNeg => Int)` called with refined lambda |
| `hof2-schmid.scala` | Closure returning `NonNeg => NonNeg` |
| `arrfold-schmid.scala` | Generic `arrFold[A]` with `arrSum` and `arrMax` |
| `rational-schmid.scala` | `Rational` class with `q != 0` constraint |

These are the programs from Georg's test suite (`LiquidTyperTests.scala`),
lightly restyled to match the first-class variants (e.g. `sumnat` is wrapped in
an object and drops the redundant `AnyInt` alias).

In addition:

- `mergeSortLength-schmid.scala` is a direct port of the first-class
  `mergeSortLength` benchmark, but it crashes the LiquidTyper and is therefore
  not benchmarked: refined class-typed method results inside the class are
  unsupported (see the comment in `SchmidBenchmarks.scala` for the error).
- `matrixDims-schmid.scala` ports the first-class `matrixDims` benchmark with
  the full dimension specifications for `transpose` and `mul`, restructured
  around LiquidTyper restrictions (top-level functions, a curried parameter
  list for `mul`'s precondition, and one function per step of the original
  `main`; see the header comment in the source file).

## Dependencies

Unmanaged jars in `lib/`, populated by `setup.sh`:

- `dotty_2.11-0.1-SNAPSHOT.jar`, `dotty-interfaces-0.1-SNAPSHOT.jar` (built from `refined-dotty/`)
- `leon_2.11-3.0.jar`, `scala-smtlib_2.11.jar` (copied from `refined-dotty/lib/`, provide the Z3 SMT-LIB interface)
- `interface-0.13.11.jar` (sbt interface for the old Dotty; copied from the Ivy cache, where the refined-dotty build resolves it, since it is not on Maven Central)

Managed dependencies (Maven Central, mirroring the refined-dotty build): `me.d-d:scala-compiler:2.11.5-20160322-171045-e19b30b3cd` (patched Scala compiler), `jline:jline:2.12`, `org.scala-lang.modules:scala-xml:1.0.1`.

## Georg's Dotty fork modifications

The fork at `mbovel/dotty@liquidtyper-fix` includes:

1. Build fixes for compatibility with modern sbt/JDK
2. Suppressed LiquidTyper debug output (`ltypr` printer set to `noPrinter`, `ctx.echo` calls commented out)
