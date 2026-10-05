package playground

import java.io.{ByteArrayOutputStream, File, PrintStream, PrintWriter}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import java.util.Comparator
import scala.util.control.NonFatal

import dotty.tools.dotc.Driver
import dotty.tools.dotc.reporting.ConsoleReporter

/** Runs the forked compiler over one snippet and returns everything it printed.
 *
 *  This is only ever called in the worker process, see [[Worker]].
 */
object Dotc:

  /** Classpath containing the scala3-library and scala-library jars, extracted from the
   *  JVM's class path property. The worker inherits it from the server process.
   */
  private val stdlibClasspath: String =
    System
      .getProperty("java.class.path", "")
      .split(File.pathSeparator)
      .filter(p => p.contains("scala3-library") || p.contains("scala-library"))
      .mkString(File.pathSeparator)

  /** Package-private: [[Store]] keys cached output on these as well as on the source. */
  private[playground] val options =
    Seq("-language:experimental.qualifiedTypes", "-color:never", "-encoding", "UTF-8")

  /** The name diagnostics refer to. The real file lives in a throwaway directory whose path
   *  has no business showing up in the output.
   */
  private val displayName = "Playground.scala"

  def compile(code: String): String =
    val buffer = ByteArrayOutputStream()
    val stream = PrintStream(buffer, true, StandardCharsets.UTF_8)
    val writer = PrintWriter(stream, true)
    // ConsoleReporter formats diagnostics exactly as the command line does; `writer` takes
    // warnings and errors, `echoer` takes INFO, and both feed the same buffer. `reader` is
    // only used by -Xprompt, which we never pass.
    val reporter = ConsoleReporter(reader = null, writer = writer, echoer = writer)
    val workDir = Files.createTempDirectory("playground-")
    try
      val source = Files.writeString(workDir.resolve(displayName), code, StandardCharsets.UTF_8)
      // -d must point at a directory that already exists.
      val target = Files.createDirectory(workDir.resolve("out"))
      val cpOptions =
        if stdlibClasspath.isEmpty then Seq("-usejavacp")
        else Seq("-classpath", stdlibClasspath)
      val args = (Seq("-d", target.toString) ++ cpOptions ++ options :+ source.toString).toArray
      // The driver reports crashes with a bare `println` and then rethrows, so redirect the
      // console too. `scala.Console` is thread-local, so this only affects this compilation.
      Console.withOut(stream):
        Console.withErr(stream):
          try
            Driver().process(args, reporter)
            ()
          catch case NonFatal(e) => e.printStackTrace(stream)
      writer.flush()
      buffer.toString(StandardCharsets.UTF_8).replace(source.toString, displayName)
    finally deleteRecursively(workDir)

  private def deleteRecursively(root: Path): Unit =
    val paths = Files.walk(root)
    try paths.sorted(Comparator.reverseOrder()).forEach(p => { Files.deleteIfExists(p); () })
    finally paths.close()
