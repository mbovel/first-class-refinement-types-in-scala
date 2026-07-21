# First-Class Refinement Types Suite

JMH compilation-time benchmarks for our qualified-types Scala 3 fork.
`FirstClassBenchmarks` compiles the `*-first-class.scala` sources from
[../sources/](../sources/) with `-language:experimental.qualifiedTypes`;
`FirstClassBaseBenchmarks` compiles the `*-first-class-base.scala`
baselines (same programs without refinements).

Requires JDK 25 and sbt. From this directory:

```sh
sbt 'bench / Jmh / run -wi 0 -i 1 FirstClassBenchmarks'           # quick test (no warmup)
sbt 'bench / Jmh / run -wi 0 -i 1 FirstClassBenchmarks.postuple'  # single benchmark
sbt 'bench / Jmh / run FirstClassBenchmarks'                      # full run (150 warmup + 20 measurement iterations)
```

See [../README.md](../README.md) for running all suites together and
generating the results table.
