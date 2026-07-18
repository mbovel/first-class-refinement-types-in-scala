package bench.compilers

import dotty.tools.dotc.Driver
import dotty.tools.dotc.reporting.Diagnostic

/** Compiler that runs Dotty with the Stainless compiler plugin.
 *
 *  Uses `-Xplugin:<stainless-assembly-jar>` to load Stainless as a compiler plugin,
 *  and adds the stainless-library jar to the classpath so that `stainless.lang._`
 *  and `stainless.annotation._` are available.
 */
object StainlessCompiler extends Compiler:
  def compile(sources: Seq[String], options: Seq[String], outputDir: String, shouldFail: Boolean = false): Unit =
    StainlessCompilers.compile(sources, options, outputDir, shouldFail, withPlugin = true)

/** Same Dotty and classpath (the stainless-library jar stays included, so
 *  `stainless.lang._` imports still resolve) but without the Stainless
 *  plugin: used by the contract-free baseline benchmarks, mirroring the
 *  feature-off baselines of the other platforms.
 */
object StainlessNoPluginCompiler extends Compiler:
  def compile(sources: Seq[String], options: Seq[String], outputDir: String, shouldFail: Boolean = false): Unit =
    StainlessCompilers.compile(sources, options, outputDir, shouldFail, withPlugin = false)

private object StainlessCompilers:

  private val stdlibClasspath: String =
    System.getProperty("java.class.path", "")
      .split(java.io.File.pathSeparator)
      .filter(p => p.contains("scala3-library") || p.contains("scala-library"))
      .mkString(java.io.File.pathSeparator)

  private val stainlessAssemblyJar: String = StainlessJars.assemblyJar
  private val stainlessLibraryJar: String = StainlessJars.libraryJar

  def compile(sources: Seq[String], options: Seq[String], outputDir: String, shouldFail: Boolean, withPlugin: Boolean): Unit =
    val fullClasspath =
      (Seq(stdlibClasspath, stainlessLibraryJar).filter(_.nonEmpty)).mkString(java.io.File.pathSeparator)
    val scalacOptions =
      (if fullClasspath.nonEmpty then Seq("-classpath", fullClasspath) else Seq.empty)
        ++ Seq("-Xno-enrich-error-messages")
        ++ (if withPlugin then Seq(s"-Xplugin:$stainlessAssemblyJar") else Seq.empty)
    val allArgs = (Array("-d", outputDir) ++ scalacOptions ++ options ++ sources)
    val reporter =
      // Extraction errors (e.g. ImperativeEliminationException) escape the Stainless plugin as
      // exceptions instead of going through the reporter; recover their source position here.
      try Driver().process(allArgs)
      catch
        case e: stainless.extraction.MalformedStainlessCode =>
          throw Exception(s"Stainless extraction failed at ${e.tree.getPos.fullString}: ${e.getMessage}", e)
    if reporter.hasErrors && !shouldFail then
      System.err.println(s"[STAINLESS-DEBUG] Assembly jar: $stainlessAssemblyJar")
      System.err.println(s"[STAINLESS-DEBUG] Library jar: $stainlessLibraryJar")
      reporter.allWarnings.foreach(w => System.err.println(s"[STAINLESS-WARNING] ${render(w)}"))
      reporter.allErrors.foreach(e => System.err.println(s"[STAINLESS-ERROR] ${render(e)}"))
      throw Exception(s"Compilation failed with errors:\n${reporter.allErrors.map(render).mkString("\n")}")
    else if !reporter.hasErrors && shouldFail then
      throw Exception("Compilation succeeded but was expected to fail")

  /** Renders a diagnostic as `file:line:column: message`, when a position is available. */
  private def render(dia: Diagnostic): String =
    val pos = dia.pos
    if pos.exists then s"${pos.source.file.path}:${pos.line + 1}:${pos.column + 1}: ${dia.message}"
    else dia.message
