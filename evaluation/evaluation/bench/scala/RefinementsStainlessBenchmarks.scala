package bench

import bench.compilers.StainlessCompiler
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

abstract class StainlessBenchmarks extends CompilationBenchmarks:

  def sourcesDir: String
  def options: Seq[String]


  @Benchmark
  def matrixDims =
    StainlessCompiler.compile(Seq(s"$sourcesDir/matrixDims.scala"), options, outDir)

  //@Benchmark
  //def range =
  //  StainlessCompiler.compile(Seq(s"$sourcesDir/range.scala"), options, outDir)

  //@Benchmark
  //def mergeSortBounds =
  //  StainlessCompiler.compile(Seq(s"$sourcesDir/mergeSortBounds.scala"), options, outDir)

  // Georg-equivalent benchmarks
  @Benchmark
  def max =
    StainlessCompiler.compile(Seq(s"$sourcesDir/max.scala"), options, outDir)

  @Benchmark
  def sumnat =
    StainlessCompiler.compile(Seq(s"$sourcesDir/sumnat.scala"), options, outDir)

  @Benchmark
  def intarray =
    StainlessCompiler.compile(Seq(s"$sourcesDir/intarray.scala"), options, outDir)

  @Benchmark
  def postuple =
    StainlessCompiler.compile(Seq(s"$sourcesDir/postuple.scala"), options, outDir)

  //@Benchmark
  //def arrfold =
  //  StainlessCompiler.compile(Seq(s"$sourcesDir/arrfold.scala"), options, outDir)

  @Benchmark
  def rational =
    StainlessCompiler.compile(Seq(s"$sourcesDir/rational.scala"), options, outDir)

/** Stainless extraction only, no verification. */
class StainlessNoVerifyBenchmarks extends StainlessBenchmarks:
  override def sourcesDir = BenchSources.dir + "/stainless"
  override def options = Seq("-P:stainless:verify:no")

/** Stainless with verification but without termination checking. */
class StainlessVerifyBenchmarks extends StainlessBenchmarks:
  override def sourcesDir = BenchSources.dir + "/stainless"
  override def options = Seq("-P:stainless:verify:yes", "-P:stainless:check-measures:no")
