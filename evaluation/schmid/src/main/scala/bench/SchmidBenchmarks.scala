package bench

import bench.compilers.SchmidCompiler
import org.openjdk.jmh.annotations.Benchmark

abstract class SchmidBenchmarks extends CompilationBenchmarks {

  /** Source file suffix, e.g. "schmid" for `../sources/max-schmid.scala`. */
  def suffix: String
  def extraOptions: Seq[String]

  def options: Seq[String] = Seq("-nowarn") ++ extraOptions

  def source(name: String): String = s"../sources/$name-$suffix.scala"

  @Benchmark
  def max(): Unit =
    SchmidCompiler.compile(Seq(source("max")), options, outDir)

  @Benchmark
  def sumnat(): Unit =
    SchmidCompiler.compile(Seq(source("sumnat")), options, outDir)

  @Benchmark
  def intarray(): Unit =
    SchmidCompiler.compile(Seq(source("intarray")), options, outDir)

  @Benchmark
  def postuple(): Unit =
    SchmidCompiler.compile(Seq(source("postuple")), options, outDir)

  @Benchmark
  def list1(): Unit =
    SchmidCompiler.compile(Seq(source("list1")), options, outDir)

  @Benchmark
  def list2(): Unit =
    SchmidCompiler.compile(Seq(source("list2")), options, outDir)

  @Benchmark
  def hof1(): Unit =
    SchmidCompiler.compile(Seq(source("hof1")), options, outDir)

  @Benchmark
  def hof2(): Unit =
    SchmidCompiler.compile(Seq(source("hof2")), options, outDir)

  @Benchmark
  def arrfold(): Unit =
    SchmidCompiler.compile(Seq(source("arrfold")), options, outDir)

  @Benchmark
  def rational(): Unit =
    SchmidCompiler.compile(Seq(source("rational")), options, outDir)

  @Benchmark
  def sqrt(): Unit =
    SchmidCompiler.compile(Seq(source("sqrt")), options, outDir)

  // Crashes the LiquidTyper: refined class-typed method results inside the
  // class are dropped ("WARNING: Ignoring ascription of unsupported type
  // LiquidType(v, SafeSeq, v.len == this.len + that.len)" for ++, take and
  // tail), and extracting ++'s qualifier then aborts with "Unknown call to
  // val len on that$0 (UnsupL<mergeSort.SafeSeq>)", since SafeSeq is
  // an unsupported type within its own body:
  // @Benchmark
  // def mergeSort(): Unit =
  //   SchmidCompiler.compile(Seq(source("mergeSort")), options, outDir)

  @Benchmark
  def matrixDims(): Unit =
    SchmidCompiler.compile(Seq(source("matrixDims")), options, outDir)
}
