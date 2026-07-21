# Georg Schmid's LiquidTyper Suite

JMH compilation-time benchmarks for Georg Schmid's 2016 LiquidTyper
extension to Dotty 0.1, using his original benchmark programs.
`SchmidRefinementBenchmarks` compiles the `*-schmid.scala` sources from
[../sources/](../sources/) (Georg's `{ v: Type if predicate }` syntax);
`SchmidBaseBenchmarks` compiles the `*-schmid-base.scala` baselines with
`-Yskip:liquidtyper`.

Requires sbt, Z3, and JDK 8 for the old Dotty fork (located via
`$JDK8_HOME`, the current `java` if it is a JDK 8, or
`cs java --jvm temurin:8`). First build the LiquidTyper Dotty fork from the
`refined-dotty` submodule (jars are copied to `lib/`, together with the
Leon and scala-smtlib jars it vendors):

```sh
./setup.sh
```

Then, from this directory:

```sh
sbt 'bench / Jmh / run -wi 0 -i 1 SchmidRefinementBenchmarks'           # quick test (no warmup)
sbt 'bench / Jmh / run -wi 0 -i 1 SchmidRefinementBenchmarks.rational'  # single benchmark
sbt 'bench / Jmh / run SchmidRefinementBenchmarks'                      # full run (150 warmup + 20 measurement iterations)
```

The fork (`mbovel/dotty@liquidtyper-fix`) is Georg's Dotty plus build fixes
for modern sbt/JDK and suppressed LiquidTyper debug output. `mergeSort` is
not benchmarked on this platform — it crashes the LiquidTyper (see the
comment in `SchmidBenchmarks.scala`) — and `matrixDims-schmid.scala` is
restructured around LiquidTyper restrictions (see its header comment).

See [../README.md](../README.md) for running all suites together and
generating the results table.
