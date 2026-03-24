package bench.compilers

import scala.quoted.*

/** Provides absolute paths to the Stainless jars, computed at compile time. */
object StainlessJars:
  inline def assemblyJar: String = ${ assemblyJarImpl }
  inline def libraryJar: String = ${ libraryJarImpl }

  private def findJar(dir: java.nio.file.Path, prefix: String): String =
    val files = java.nio.file.Files.list(dir).iterator
    var result: String = null
    while files.hasNext do
      val f = files.next()
      if f.getFileName.toString.startsWith(prefix) && f.getFileName.toString.endsWith(".jar") then
        result = f.toAbsolutePath.normalize.toString
    if result == null then
      throw RuntimeException(s"No jar starting with '$prefix' found in $dir")
    result

  private def evaluationDir(using Quotes): java.nio.file.Path =
    import quotes.reflect.*
    val thisFile = java.nio.file.Paths.get(Position.ofMacroExpansion.sourceFile.path)
    // This file is at evaluation/bench/scala/compilers/StainlessJars.scala
    // evaluation/ is 4 levels up
    thisFile.getParent.getParent.getParent.getParent.toAbsolutePath.normalize

  private def assemblyJarImpl(using Quotes): Expr[String] =
    val evalDir = evaluationDir
    val targetDir = evalDir.resolve("stainless/frontends/dotty/target")
    // Find the scala version subdirectory
    val scalaDir = java.nio.file.Files.list(targetDir).iterator
    var found: java.nio.file.Path = null
    while scalaDir.hasNext do
      val d = scalaDir.next()
      if d.getFileName.toString.startsWith("scala-") then found = d
    val jar = findJar(found, "stainless-dotty-assembly")
    Expr(jar)

  private def libraryJarImpl(using Quotes): Expr[String] =
    val evalDir = evaluationDir
    val targetDir = evalDir.resolve("stainless/frontends/library/target")
    val scalaDir = java.nio.file.Files.list(targetDir).iterator
    var found: java.nio.file.Path = null
    while scalaDir.hasNext do
      val d = scalaDir.next()
      if d.getFileName.toString.startsWith("scala-") then found = d
    val jar = findJar(found, "stainless-library")
    Expr(jar)

