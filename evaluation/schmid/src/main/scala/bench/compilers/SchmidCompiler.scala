package bench.compilers

import dotty.tools.dotc.Main
import dotty.tools.dotc.liquidtyper.{Inference, Qualifier}
import dotty.tools.dotc.liquidtyper.extraction.LeonExtractor

/** Compiler wrapper that calls Georg Schmid's LiquidTyper-enabled Dotty. */
object SchmidCompiler {

  // The LiquidTyper keeps JVM-global caches keyed by (types wrapping) dotty
  // symbols, which pin past runs' entire symbol tables and classpath data:
  // after ~120 in-process compilations the 8G benchmark fork dies of GC
  // overhead. Clearing them before each compilation restores fresh-JVM
  // semantics (each is repopulated lazily):
  //  - LeonExtractor._subjectVarId/_thisVarId (private, hence reflection)
  //  - Inference.groundQuals, whose ground qualifiers reference identifiers
  //    typed LeonObjectType(classSymbol), leaking one universe per compiled
  //    class-bearing source
  private val leakyCacheFields = Seq("_subjectVarId", "_thisVarId").map { name =>
    val field = LeonExtractor.getClass.getDeclaredField(name)
    field.setAccessible(true)
    field
  }

  private def resetLiquidTyperCaches(): Unit = {
    for (field <- leakyCacheFields)
      field.get(LeonExtractor).asInstanceOf[scala.collection.mutable.Map[_, _]].clear()
    Inference.groundQuals.clear()
    Inference.groundQuals += Qualifier.True -> Inference.qualIdTop
  }

  def compile(sources: Seq[String], options: Seq[String], outputDir: String, shouldFail: Boolean = false): Unit = {
    resetLiquidTyperCaches()
    val allArgs = (Array("-d", outputDir, "-usejavacp") ++ options ++ sources)
    val reporter = Main.process(allArgs)
    if (reporter.hasErrors && !shouldFail)
      throw new Exception("Compilation failed with errors")
    else if (!reporter.hasErrors && shouldFail)
      throw new Exception("Compilation succeeded but was expected to fail")
  }
}
