package bench

import bench.compilers.DottyCompiler
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

abstract class AbstractFirstClassBenchmarks extends CompilationBenchmarks:

  /** Source file suffix, e.g. "first-class" for `sources/max-first-class.scala`. */
  def suffix: String
  def options: Seq[String]

  def source(name: String): String = s"${BenchSources.dir}/$name-$suffix.scala"

  @Benchmark
  def maxAbstract =
    DottyCompiler.compile(Seq(source("maxAbstract")), options, outDir)

  @Benchmark
  def maxAbstractBig =
    DottyCompiler.compile(Seq(source("maxAbstractBig")), options, outDir)

  @Benchmark
  def sqrt =
    DottyCompiler.compile(Seq(source("sqrt")), options, outDir)

  @Benchmark
  def vec =
    DottyCompiler.compile(Seq(source("vec")), options, outDir)

  @Benchmark
  def matrix =
    DottyCompiler.compile(Seq(source("matrix")), options, outDir)

  @Benchmark
  def matrixDims =
    DottyCompiler.compile(Seq(source("matrixDims")), options, outDir)

  @Benchmark
  def range =
    DottyCompiler.compile(Seq(source("range")), options, outDir)

  @Benchmark
  def mergeSortLength =
    DottyCompiler.compile(Seq(source("mergeSortLength")), options, outDir)

  @Benchmark
  def fibMemo =
    DottyCompiler.compile(Seq(source("fibMemo")), options, outDir)

  // Georg-equivalent benchmarks
  @Benchmark
  def max =
    DottyCompiler.compile(Seq(source("max")), options, outDir)

  @Benchmark
  def sumnat =
    DottyCompiler.compile(Seq(source("sumnat")), options, outDir)

  @Benchmark
  def intarray =
    DottyCompiler.compile(Seq(source("intarray")), options, outDir)

  @Benchmark
  def postuple =
    DottyCompiler.compile(Seq(source("postuple")), options, outDir)

  @Benchmark
  def list1 =
    DottyCompiler.compile(Seq(source("list1")), options, outDir)

  @Benchmark
  def list2 =
    DottyCompiler.compile(Seq(source("list2")), options, outDir)

  @Benchmark
  def hof1 =
    DottyCompiler.compile(Seq(source("hof1")), options, outDir)
  
  @Benchmark
  def hof2 =
    DottyCompiler.compile(Seq(source("hof2")), options, outDir)

  @Benchmark
  def fansi =
    DottyCompiler.compile(Seq(source("fansi")), options, outDir)

  @Benchmark
  def collect =
    DottyCompiler.compile(Seq(source("collect")), options, outDir)
  // @Benchmark
  // def arrfold =
  //   DottyCompiler.compile(Seq(source("arrfold")), options, outDir)

  @Benchmark
  def rational =
    DottyCompiler.compile(Seq(source("rational")), options, outDir)
