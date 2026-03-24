package bench

import scala.quoted.*

/** Provides the absolute path to the `bench-sources` directory,
 *  computed at compile time relative to this source file's location.
 */
object BenchSources:
  /** Absolute path to the `bench-sources` directory. */
  inline def dir: String = ${ dirImpl }

  private def dirImpl(using Quotes): Expr[String] =
    import quotes.reflect.*
    val thisFile = java.nio.file.Paths.get(Position.ofMacroExpansion.sourceFile.path)
    // This file is at evaluation/bench/scala/BenchSources.scala
    // bench-sources is at evaluation/bench-sources
    val benchSources = thisFile.getParent.getParent.getParent.resolve("bench-sources").toAbsolutePath.normalize
    Expr(benchSources.toString)
