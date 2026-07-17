package bench

/** Quick test to check if SchmidCompiler works. Run with:
 *  sbt 'set fork := true' 'runMain bench.TestCompile'
 */
object TestCompile {
  def main(args: Array[String]): Unit = {
    val dir = "out"
    new java.io.File(dir).mkdirs()
    val files = Seq("max", "sumnat", "intarray", "postuple", "list1", "list2",
                    "hofsafety1", "hofsafety2", "arrfold", "rational")
    for (f <- files) {
      print(s"Testing $f.scala... ")
      try {
        bench.compilers.SchmidCompiler.compile(Seq(s"../sources/$f-schmid.scala"), Seq(), dir)
        println("OK")
      } catch {
        case e: Exception => println(s"FAILED: ${e.getMessage}")
      }
    }
  }
}
