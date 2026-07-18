package bench

import bench.compilers.{Compiler, StainlessCompiler}
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

  @Benchmark
  def sumnat =
    compiler.compile(Seq(source("sumnat")), options, outDir)

  @Benchmark
  def intarray =
    compiler.compile(Seq(source("intarray")), options, outDir)

  @Benchmark
  def postuple =
    compiler.compile(Seq(source("postuple")), options, outDir)

  //@Benchmark
  //def arrfold =
  //  compiler.compile(Seq(source("arrfold")), options, outDir)

  @Benchmark
  def rational =
    compiler.compile(Seq(source("rational")), options, outDir)

/** Baseline: Stainless extraction only, no verification. */
class StainlessBaseBenchmarks extends StainlessBenchmarks:
  override def suffix = "stainless"
  override def options = Seq("-P:stainless:verify:no")

/** Stainless with verification (including termination measures; the plugin
 *  only understands the verify and ghost-elim options). */
class StainlessVerifyBenchmarks extends StainlessBenchmarks:
  override def suffix = "stainless"
  override def options = Seq("-P:stainless:verify:yes")
