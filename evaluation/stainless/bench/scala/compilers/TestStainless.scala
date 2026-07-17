package bench.compilers

object TestStainless:
  def main(args: Array[String]): Unit =
    try
      StainlessCompiler.compile(
        Seq(s"${bench.BenchSources.dir}/mergeSortBounds-stainless.scala"),
        Seq("-P:stainless:verify:yes", "-P:stainless:check-measures:no"),
        "out"
      )
      println("SUCCESS")
    catch case e: Exception =>
      println(s"FAILED: ${e.getMessage}")
