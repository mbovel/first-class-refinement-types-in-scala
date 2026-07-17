package bench.compilers

/** Compiles a single benchmark source with the Stainless compiler, for debugging outside JMH.
 *
 *  Usage: bench/runMain bench.compilers.stainlessCompileOne <file> [options...]
 */
@main def stainlessCompileOne(file: String, options: String*): Unit =
  val outDir = java.nio.file.Files.createTempDirectory("bench-out").toString
  StainlessCompiler.compile(Seq(file), options, outDir)
