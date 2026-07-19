package bench.compilers

import dotty.tools.dotc.Main
import dotty.tools.dotc.liquidtyper.extraction.LeonExtractor

/** Compiler wrapper that calls Georg Schmid's LiquidTyper-enabled Dotty. */
object SchmidCompiler {

  // The LeonExtractor singleton caches identifiers in maps keyed by dotty
  // symbols and Leon types wrapping them, which pins every past run's entire
  // symbol table: after ~120 in-process compilations the 8G benchmark fork
  // dies of GC overhead. Both maps are repopulated lazily, so clearing them
  // before each compilation restores fresh-JVM semantics.
  private val leakyCacheFields = Seq("_subjectVarId", "_thisVarId").map { name =>
    val field = LeonExtractor.getClass.getDeclaredField(name)
    field.setAccessible(true)
    field
  }

  private def resetLeonExtractorCaches(): Unit =
    for (field <- leakyCacheFields)
      field.get(LeonExtractor).asInstanceOf[scala.collection.mutable.Map[_, _]].clear()

  def compile(sources: Seq[String], options: Seq[String], outputDir: String, shouldFail: Boolean = false): Unit = {
    resetLeonExtractorCaches()
    val allArgs = (Array("-d", outputDir, "-usejavacp") ++ options ++ sources)
    val reporter = Main.process(allArgs)
    if (reporter.hasErrors && !shouldFail)
      throw new Exception("Compilation failed with errors")
    else if (!reporter.hasErrors && shouldFail)
      throw new Exception("Compilation succeeded but was expected to fail")
  }
}
