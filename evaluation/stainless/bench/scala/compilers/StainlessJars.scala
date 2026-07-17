package bench.compilers

import scala.quoted.*

/** Provides absolute paths to the Stainless jars, computed at compile time. */
object StainlessJars:
  inline def assemblyJar: String = ${ jarImpl("stainless-assembly.jar") }
  inline def libraryJar: String = ${ jarImpl("stainless-library.jar") }

  private def jarImpl(name: String)(using Quotes): Expr[String] =
    import quotes.reflect.*
    val thisFile = java.nio.file.Paths.get(Position.ofMacroExpansion.sourceFile.path)
    // This file is at bench/scala/compilers/StainlessJars.scala
    // Project root is 4 levels up
    val jar = thisFile.getParent.getParent.getParent.getParent.resolve("lib").resolve(name).toAbsolutePath.normalize
    if !java.nio.file.Files.exists(jar) then
      report.errorAndAbort(s"Stainless jar not found: $jar. Run ./setup.sh first.")
    Expr(jar.toString)
