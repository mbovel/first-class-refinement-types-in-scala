package bench

import bench.compilers.{Compiler, StainlessCompiler}
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

abstract class StainlessBenchmarks extends CompilationBenchmarks:

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
  def mergeSortLength =
    compiler.compile(Seq(source("mergeSortLength")), options, outDir)

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
