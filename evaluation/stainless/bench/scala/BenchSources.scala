package bench

import scala.quoted.*

/** Provides the absolute path to the shared `evaluation/sources` directory,
 *  computed at compile time relative to this source file's location.
 */
object BenchSources:
  /** Absolute path to the `sources` directory. */
  inline def dir: String = ${ dirImpl }

  private def dirImpl(using Quotes): Expr[String] =
    import quotes.reflect.*
    val thisFile = java.nio.file.Paths.get(Position.ofMacroExpansion.sourceFile.path)
    // This file is at evaluation/<project>/bench/scala/BenchSources.scala
    // Sources are at evaluation/sources
    val sources = thisFile.getParent.getParent.getParent.getParent.resolve("sources").toAbsolutePath.normalize
    Expr(sources.toString)
