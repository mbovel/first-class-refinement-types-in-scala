package bench.compilers

import dotty.tools.dotc.Main

/** Compiler wrapper that calls Georg Schmid's LiquidTyper-enabled Dotty. */
object SchmidCompiler {

  def compile(sources: Seq[String], options: Seq[String], outputDir: String, shouldFail: Boolean = false): Unit = {
    val allArgs = (Array("-d", outputDir, "-usejavacp") ++ options ++ sources)
    val reporter = Main.process(allArgs)
    if (reporter.hasErrors && !shouldFail)
      throw new Exception("Compilation failed with errors")
    else if (!reporter.hasErrors && shouldFail)
      throw new Exception("Compilation succeeded but was expected to fail")
  }
}
