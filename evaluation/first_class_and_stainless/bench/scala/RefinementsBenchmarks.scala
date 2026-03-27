package bench

import bench.compilers.DottyCompiler
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

abstract class RefinementsBenchmarks extends CompilationBenchmarks:

  def sourcesDir: String
  def options: Seq[String]

  @Benchmark
  def maximum =
    DottyCompiler.compile(Seq(s"$sourcesDir/maximum.scala"), options, outDir) 
  
  @Benchmark
  def maximumBig =
    DottyCompiler.compile(Seq(s"$sourcesDir/maximumBig.scala"), options, outDir) 

  @Benchmark
  def vec =
    DottyCompiler.compile(Seq(s"$sourcesDir/vec.scala"), options, outDir)

  @Benchmark
  def matrix =
    DottyCompiler.compile(Seq(s"$sourcesDir/matrix.scala"), options, outDir)

  @Benchmark
  def matrixDims =
    DottyCompiler.compile(Seq(s"$sourcesDir/matrixDims.scala"), options, outDir)

  @Benchmark
  def range =
    DottyCompiler.compile(Seq(s"$sourcesDir/range.scala"), options, outDir)

  @Benchmark
  def mergeSortBounds =
    DottyCompiler.compile(Seq(s"$sourcesDir/mergeSortBounds.scala"), options, outDir)

  @Benchmark
  def fibMemo =
    DottyCompiler.compile(Seq(s"$sourcesDir/fibMemo.scala"), options, outDir)

  // Georg-equivalent benchmarks
  // @Benchmark
  // def max =
  //   DottyCompiler.compile(Seq(s"$sourcesDir/max.scala"), options, outDir)

  // @Benchmark
  // def sumnat =
  //   DottyCompiler.compile(Seq(s"$sourcesDir/sumnat.scala"), options, outDir)

  @Benchmark
  def intarray =
    DottyCompiler.compile(Seq(s"$sourcesDir/intarray.scala"), options, outDir)

  @Benchmark
  def postuple =
    DottyCompiler.compile(Seq(s"$sourcesDir/postuple.scala"), options, outDir)

  @Benchmark
  def list1 =
    DottyCompiler.compile(Seq(s"$sourcesDir/list1.scala"), options, outDir)

  @Benchmark
  def list2 =
    DottyCompiler.compile(Seq(s"$sourcesDir/list2.scala"), options, outDir)

  @Benchmark
  def hofsafety1 =
    DottyCompiler.compile(Seq(s"$sourcesDir/hofsafety1.scala"), options, outDir)

  @Benchmark
  def fansi =
    DottyCompiler.compile(Seq(s"$sourcesDir/fansi.scala"), options, outDir)

  @Benchmark
  def collect =
    DottyCompiler.compile(Seq(s"$sourcesDir/collect.scala"), options, outDir)

  // @Benchmark
  // def hofsafety2 =
  //   DottyCompiler.compile(Seq(s"$sourcesDir/hofsafety2.scala"), options, outDir)

  // @Benchmark
  // def arrfold =
  //   DottyCompiler.compile(Seq(s"$sourcesDir/arrfold.scala"), options, outDir)

  // @Benchmark
  // def rational =
  //   DottyCompiler.compile(Seq(s"$sourcesDir/rational.scala"), options, outDir)
