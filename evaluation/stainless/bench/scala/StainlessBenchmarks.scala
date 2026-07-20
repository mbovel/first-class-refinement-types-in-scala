package bench

import bench.compilers.{Compiler, StainlessCompiler, StainlessNoPluginCompiler}
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

abstract class StainlessBenchmarks extends CompilationBenchmarks:

  // Verification should run on native Z3: on platforms without ScalaZ3
  // bindings (e.g. ARM), inox falls back to other solvers such as Princess,
  // which changes what is measured. Warn loudly so fallback runs are never
  // mistaken for native-Z3 results.
  if !inox.solvers.SolverFactory.hasNativeZ3 then
    System.err.println(
      "[STAINLESS-BENCH] WARNING: native Z3 bindings (ScalaZ3) are not available on this platform; " +
        "inox will fall back to another solver (e.g. Princess). Results are NOT comparable to native-Z3 runs.")

  /** Source file suffix, e.g. "stainless" for `sources/max-stainless.scala`. */
  def suffix: String
  def options: Seq[String]
  def compiler: Compiler = StainlessCompiler

  def source(name: String): String = s"${BenchSources.dir}/$name-$suffix.scala"

  @Benchmark
  def matrixDims =
    compiler.compile(Seq(source("matrixDims")), options, outDir)

  @Benchmark
  def vec =
    compiler.compile(Seq(source("vec")), options, outDir)

  @Benchmark
  def mergeSort =
    compiler.compile(Seq(source("mergeSort")), options, outDir)

  // Georg-equivalent benchmarks
  @Benchmark
  def max =
    compiler.compile(Seq(source("max")), options, outDir)

  @Benchmark
  def sqrt =
    compiler.compile(Seq(source("sqrt")), options, outDir)

  // Z3 non-deterministically diverges on one of sumnat's VCs: most
  // iterations verify in ~0.5 s, but a few percent hit repeated 30 s solver
  // timeouts and take minutes, ruining the measurements.
  // See https://github.com/epfl-lara/stainless/issues/1766
  // @Benchmark
  // def sumnat =
  //   compiler.compile(Seq(source("sumnat")), options, outDir)

  @Benchmark
  def intarray =
    compiler.compile(Seq(source("intarray")), options, outDir)

  @Benchmark
  def postuple =
    compiler.compile(Seq(source("postuple")), options, outDir)

  @Benchmark
  def rational =
    compiler.compile(Seq(source("rational")), options, outDir)

/** Baseline: contract-free sources (no require/ensuring/decreases) compiled
 *  with the same Dotty and classpath but without the Stainless plugin,
 *  mirroring the feature-off baselines of the other platforms. */
class StainlessBaseBenchmarks extends StainlessBenchmarks:
  override def suffix = "stainless-base"
  override def compiler = StainlessNoPluginCompiler
  override def options = Seq()

/** Stainless with verification (including termination measures; the plugin
 *  only understands the verify and ghost-elim options). */
class StainlessVerifyBenchmarks extends StainlessBenchmarks:
  override def suffix = "stainless"
  override def options = Seq("-P:stainless:verify:yes")
