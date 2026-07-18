package bench

import bench.compilers.StainlessCompiler

/** Quick test to check if StainlessCompiler works. Run with:
 *  sbt 'bench / runMain bench.TestCompile'
 *  Optionally pass benchmark names to test only those, e.g.
 *  sbt 'bench / runMain bench.TestCompile sumnat'
 */
object TestCompile {
  def main(args: Array[String]): Unit = {
    val dir = "out"
    new java.io.File(dir).mkdirs()
    val defaultFiles = Seq("max", "sqrt", "sumnat", "intarray", "postuple", "rational", "matrixDims", "vec")
    val files = if (args.nonEmpty) args.toSeq else defaultFiles
    val options = Seq("-P:stainless:verify:yes", "-P:stainless:check-measures:no")
    for (f <- files) {
      println(s"Testing $f.scala... ")
      try {
        StainlessCompiler.compile(Seq(s"${BenchSources.dir}/$f-stainless.scala"), options, dir)
        println(s"$f OK")
      } catch {
        case e: Throwable => println(s"$f FAILED: ${e.getMessage}")
      }
    }
  }
}
