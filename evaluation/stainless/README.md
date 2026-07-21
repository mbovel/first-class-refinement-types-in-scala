# Stainless Suite

JMH compilation-time benchmarks for Stainless run as a Dotty compiler
plugin. `StainlessVerifyBenchmarks` compiles the `*-stainless.scala`
sources from [../sources/](../sources/) with extraction and verification
enabled (`-P:stainless:verify:yes`, native Z3; per-VC timeout and other
verification options in [stainless.conf](stainless.conf));
`StainlessBaseBenchmarks` compiles the contract-free
`*-stainless-base.scala` baselines with the same Dotty and classpath but
without the plugin.

Requires JDK 25, sbt, and Z3. First build the Stainless plugin from the
vendored fork submodule (jars are copied to `lib/`):

```sh
./setup.sh
```

Then, from this directory:

```sh
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessVerifyBenchmarks'             # quick test (no warmup)
sbt 'bench / Jmh / run -wi 0 -i 1 StainlessVerifyBenchmarks.matrixDims'  # single benchmark
sbt 'bench / Jmh / run StainlessVerifyBenchmarks'                        # full run (150 warmup + 20 measurement iterations)
```

The fork (`mbovel/stainless@refinement-types-eval-v0.9.9.3`) is the
released `v0.9.9.3` plus benchmark-specific changes: ScalaZ3 natives
bundled in the assembly jar, verification failures reported as Dotty
compilation errors, and non-error reporter output suppressed.

See [../README.md](../README.md) for running all suites together and
generating the results table.
