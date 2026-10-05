package playground

import java.io.{ByteArrayOutputStream, File, PrintStream, PrintWriter, StringWriter}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import java.util.Comparator
import java.util.concurrent.{Callable, ExecutionException, Executors, TimeUnit, TimeoutException}
import scala.concurrent.duration.*
import scala.util.control.NonFatal

import dotty.tools.dotc.Driver
import dotty.tools.dotc.reporting.ConsoleReporter

/** Compiles a snippet with the forked compiler and returns what it printed. */
object Compile:

  /** Either what the compiler printed, or a signal that it ran for too long. */
  enum Result:
    case Output(text: String)
    case TimedOut

  private val timeout = sys.env.get("PLAYGROUND_TIMEOUT").fold(30)(_.toInt).seconds

  /** Classpath containing the scala3-library and scala-library jars, extracted from the
   *  JVM's class path property. Requires a forked JVM, see `fork` in build.sbt.
   */
  private val stdlibClasspath: String =
    System
      .getProperty("java.class.path", "")
      .split(File.pathSeparator)
      .filter(p => p.contains("scala3-library") || p.contains("scala-library"))
      .mkString(File.pathSeparator)

  private val options =
    Seq("-language:experimental.qualifiedTypes", "-color:never", "-encoding", "UTF-8")

  /** The name diagnostics refer to. The real file lives in a throwaway directory whose path
   *  has no business showing up in the output.
   */
  private val displayName = "Playground.scala"

  /** Compilations all run on this one thread. That serializes them, which they need -- the
   *  compiler keeps global mutable state and cask serves requests from a thread pool -- and
   *  it gives the deeply recursive typer a far larger stack than a worker thread would.
   */
  private val executor = Executors.newSingleThreadExecutor: run =>
    Thread.ofPlatform().name("dotc").daemon().stackSize(32L * 1024 * 1024).unstarted(run)

  def apply(code: String): Result =
    val task: Callable[String] = () => compile(code)
    val pending = executor.submit(task)
    try Result.Output(pending.get(timeout.toSeconds, TimeUnit.SECONDS))
    catch
      case _: TimeoutException =>
        // Best effort: the compiler never polls for interrupts, so this frees the request
        // but the thread may well stay busy, delaying whatever is queued behind it.
        pending.cancel(true)
        Result.TimedOut
      case e: ExecutionException =>
        Result.Output(stackTrace(Option(e.getCause).getOrElse(e)))

  private def compile(code: String): String =
    // An earlier compilation may have been interrupted on timeout and left the flag set,
    // which would make interruptible I/O here fail for no reason.
    Thread.interrupted()
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

  private def stackTrace(e: Throwable): String =
    val out = StringWriter()
    e.printStackTrace(PrintWriter(out))
    out.toString

  private def deleteRecursively(root: Path): Unit =
    val paths = Files.walk(root)
    try paths.sorted(Comparator.reverseOrder()).forEach(p => { Files.deleteIfExists(p); () })
    finally paths.close()
