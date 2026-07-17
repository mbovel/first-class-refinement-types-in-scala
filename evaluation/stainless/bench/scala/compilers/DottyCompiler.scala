package bench.compilers

import dotty.tools.dotc.Driver

/** Compiler that directly calls Dotty's Driver API.
 *
 *  This is a simpler approach that bypasses the sbt bridge interface.
 */
object DottyCompiler extends Compiler:
  /** Classpath containing the scala3-library and scala-library jars,
   *  extracted from the JVM's class path property.
   */
  private val stdlibClasspath: String =
    System.getProperty("java.class.path", "")
      .split(java.io.File.pathSeparator)
      .filter(p => p.contains("scala3-library") || p.contains("scala-library"))
      .mkString(java.io.File.pathSeparator)

  def compile(sources: Seq[String], options: Seq[String], outputDir: String, shouldFail: Boolean = false): Unit =
    val cpOptions = if stdlibClasspath.nonEmpty then Seq("-classpath", stdlibClasspath) else Seq.empty
    val allArgs = (Array("-d", outputDir) ++ cpOptions ++ options ++ sources)
    val reporter = Driver().process(allArgs)
    if reporter.hasErrors && !shouldFail then
      throw Exception(s"Compilation failed with errors: ${reporter.allErrors.mkString("\n")}")
    else if !reporter.hasErrors && shouldFail then
      throw Exception("Compilation succeeded but was expected to fail")
