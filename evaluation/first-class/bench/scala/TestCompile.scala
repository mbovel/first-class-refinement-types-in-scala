package bench

import bench.compilers.DottyCompiler

/** Quick test to check if DottyCompiler works. Run with:
 *  sbt 'bench / runMain bench.TestCompile'
 *  Optionally pass benchmark names to test only those, e.g.
 *  sbt 'bench / runMain bench.TestCompile sqrt'
 */
object TestCompile {
  def main(args: Array[String]): Unit = {
    val dir = "out"
    new java.io.File(dir).mkdirs()
    val defaultFiles = Seq("maxAbstract", "maxAbstractBig", "sqrt", "vec", "matrix",
                           "matrixDims", "range", "fibMemo", "max", "arrfold", "intarray", "postuple",
                           "list1", "list2", "hof1", "hof2", "fansi", "collect")
    val files = if (args.nonEmpty) args.toSeq else defaultFiles
    val options = Seq("-language:experimental.qualifiedTypes")
    for (f <- files) {
      print(s"Testing $f.scala... ")
      try {
        DottyCompiler.compile(Seq(s"${BenchSources.dir}/$f-first-class.scala"), options, dir)
        println("OK")
      } catch {
        case e: Throwable => println(s"FAILED: ${e.getMessage}")
      }
    }
  }
}
