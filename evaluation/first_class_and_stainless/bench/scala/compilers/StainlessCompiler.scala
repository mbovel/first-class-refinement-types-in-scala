package bench.compilers

import dotty.tools.dotc.Driver

/** Compiler that runs Dotty with the Stainless compiler plugin.
 *
 *  Uses `-Xplugin:<stainless-assembly-jar>` to load Stainless as a compiler plugin,
 *  and adds the stainless-library jar to the classpath so that `stainless.lang._`
 *  and `stainless.annotation._` are available.
 */
object StainlessCompiler extends Compiler:

  private val stdlibClasspath: String =
    System.getProperty("java.class.path", "")
      .split(java.io.File.pathSeparator)
      .filter(p => p.contains("scala3-library") || p.contains("scala-library"))
      .mkString(java.io.File.pathSeparator)

  private val stainlessAssemblyJar: String = StainlessJars.assemblyJar
  private val stainlessLibraryJar: String = StainlessJars.libraryJar

  def compile(sources: Seq[String], options: Seq[String], outputDir: String, shouldFail: Boolean = false): Unit =
    val fullClasspath =
      (Seq(stdlibClasspath, stainlessLibraryJar).filter(_.nonEmpty)).mkString(java.io.File.pathSeparator)
    val cpOptions = if fullClasspath.nonEmpty then Seq("-classpath", fullClasspath) else Seq.empty
    val pluginOptions = Seq(s"-Xplugin:$stainlessAssemblyJar")
    val allArgs = (Array("-d", outputDir) ++ cpOptions ++ pluginOptions ++ options ++ sources)
    val reporter = Driver().process(allArgs)
    if reporter.hasErrors && !shouldFail then
      System.err.println(s"[STAINLESS-DEBUG] Assembly jar: $stainlessAssemblyJar")
      System.err.println(s"[STAINLESS-DEBUG] Library jar: $stainlessLibraryJar")
      System.err.println(s"[STAINLESS-DEBUG] All warnings: ${reporter.allWarnings.map(w => w.message).mkString("; ")}")
      reporter.allErrors.foreach(e => System.err.println(s"[STAINLESS-ERROR] ${e.message} at ${e.pos}"))
      throw Exception(s"Compilation failed with errors: ${reporter.allErrors.mkString("\n")}")
    else if !reporter.hasErrors && shouldFail then
      throw Exception("Compilation succeeded but was expected to fail")
