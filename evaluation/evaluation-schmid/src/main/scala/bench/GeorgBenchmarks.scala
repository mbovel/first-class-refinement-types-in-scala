package bench

import bench.compilers.GeorgCompiler
import org.openjdk.jmh.annotations.Benchmark

abstract class GeorgBenchmarks extends CompilationBenchmarks {

  def sourcesDir: String
  def extraOptions: Seq[String]

  def options: Seq[String] = Seq("-nowarn") ++ extraOptions

  @Benchmark
  def max(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/max.scala"), options, outDir)

  @Benchmark
  def sumnat(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/sumnat.scala"), options, outDir)

  @Benchmark
  def intarray(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/intarray.scala"), options, outDir)

  @Benchmark
  def postuple(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/postuple.scala"), options, outDir)

  @Benchmark
  def list1(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/list1.scala"), options, outDir)

  @Benchmark
  def list2(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/list2.scala"), options, outDir)

  @Benchmark
  def hofsafety1(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/hofsafety1.scala"), options, outDir)

  @Benchmark
  def hofsafety2(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/hofsafety2.scala"), options, outDir)

  @Benchmark
  def arrfold(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/arrfold.scala"), options, outDir)

  @Benchmark
  def rational(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/rational.scala"), options, outDir)

  @Benchmark
  def matrixDims(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/matrixDims.scala"), options, outDir)

  @Benchmark
  def mergeSortBounds(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/mergeSortBounds.scala"), options, outDir)

  @Benchmark
  def linearSortBounds(): Unit =
    GeorgCompiler.compile(Seq(s"$sourcesDir/linearSortBounds.scala"), options, outDir)
}
