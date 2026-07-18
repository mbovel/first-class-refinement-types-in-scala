package bench

/** Quick test to check if SchmidCompiler works. Run with:
 *  sbt 'set fork := true' 'runMain bench.TestCompile'
 *  Optionally pass benchmark names to test only those, e.g.
 *  sbt 'set fork := true' 'runMain bench.TestCompile mergeSortLength'
 */
object TestCompile {
  def main(args: Array[String]): Unit = {
    val dir = "out"
    new java.io.File(dir).mkdirs()
    val defaultFiles = Seq("max", "sumnat", "intarray", "postuple", "list1", "list2",
                           "hof1", "hof2", "arrfold", "rational", "sqrt", "matrixDims")
    val files = if (args.nonEmpty) args.toSeq else defaultFiles
    for (f <- files) {
      print(s"Testing $f.scala... ")
      try {
        bench.compilers.SchmidCompiler.compile(Seq(s"../sources/$f-schmid.scala"), Seq(), dir)
        println("OK")
      } catch {
        case e: Throwable => println(s"FAILED: ${e.getMessage}")
      }
    }
  }
}
