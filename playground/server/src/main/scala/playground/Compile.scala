package playground

import java.io.{
  BufferedInputStream, BufferedOutputStream, DataInputStream, DataOutputStream, File,
  IOException, PrintWriter, StringWriter,
}
import java.util.concurrent.{Callable, ExecutionException, Executors, TimeUnit, TimeoutException}
import scala.concurrent.duration.*
import scala.jdk.OptionConverters.*

/** Compiles snippets in a child process.
 *
 *  Not in this process, because the compiler cannot be stopped: it never polls for
 *  interrupts, so a snippet that makes it loop would occupy its thread for good and every
 *  later request would queue behind it. A child can be killed outright. It is kept alive
 *  between requests because starting one costs about five seconds, against well under a
 *  second once warm.
 */
object Compile:

  /** Either what the compiler printed, or a signal that it ran for too long. */
  enum Result:
    case Output(text: String)
    case TimedOut

  private val timeout = sys.env.get("PLAYGROUND_TIMEOUT").fold(30)(_.toInt).seconds

  /** One worker behind one pipe, so exchanges happen one at a time. */
  private val exchanges = Executors.newSingleThreadExecutor: run =>
    Thread.ofPlatform().name("compile").daemon().unstarted(run)

  private final class Child:
    val process: Process = spawn()
    val requests = DataOutputStream(BufferedOutputStream(process.getOutputStream))
    val responses = DataInputStream(BufferedInputStream(process.getInputStream))

  @volatile private var current: Child | Null = null

  def apply(code: String): Result =
    Store.get(code) match
      case Some(output) => Result.Output(output)
      case None =>
        val result = compile(code)
        // A timeout says nothing durable about the program, only about the worker that was
        // running when it fired, so it is not worth remembering.
        result match
          case Result.Output(text) => Store.put(code, text)
          case Result.TimedOut => ()
        result

  private def compile(code: String): Result =
    val task: Callable[String] = () => exchange(code)
    val pending = exchanges.submit(task)
    try Result.Output(pending.get(timeout.toSeconds, TimeUnit.SECONDS))
    catch
      case _: TimeoutException =>
        // Killing the worker is what makes this recoverable, and it also unblocks the read
        // in `exchange`, so no thread is left stuck behind a compilation nobody wants.
        discard()
        Result.TimedOut
      case e: ExecutionException =>
        Result.Output(stackTrace(Option(e.getCause).getOrElse(e)))

  /** Starting a worker costs seconds. Do it before the first visitor rather than during.
   *
   *  Deliberately not through [[apply]]: starting a worker and loading the compiler into it
   *  can take longer than a request is allowed to, and timing out here would kill the very
   *  worker this is meant to start. Requests queue behind it, which is the point.
   */
  def warmUp(): Unit =
    val task: Callable[String] = () => exchange("class WarmUp")
    exchanges.submit(task)
    ()

  private def exchange(code: String): String =
    val child = worker()
    try talk(child, code)
    catch
      // A worker that died mid-compile, out of memory say, takes its pipe with it. Retrying
      // once on a fresh worker tells that apart from a snippet that kills every worker.
      // The guard excludes the other way a pipe breaks: `discard` having killed this worker
      // on a timeout, in which case nobody is waiting for an answer any more.
      case _: IOException if current eq child =>
        discard()
        talk(worker(), code)

  private def talk(child: Child, code: String): String =
    Framing.write(child.requests, code)
    Framing.read(child.responses)

  private def worker(): Child =
    val existing = current
    if existing != null && existing.process.isAlive then existing
    else
      val fresh = Child()
      current = fresh
      fresh

  private def discard(): Unit =
    val existing = current
    current = null
    if existing != null then existing.process.destroyForcibly()
    ()

  private def spawn(): Process =
    // The worker is this same application, started at a different main class, so it needs
    // no classpath of its own.
    val java = ProcessHandle.current.info.command.toScala.getOrElse(
      Seq(System.getProperty("java.home"), "bin", "java").mkString(File.separator),
    )
    val command = List(java, "-Xmx2g", "-cp", System.getProperty("java.class.path"), "playground.Worker")
    ProcessBuilder(command*)
      // Compiler output comes back over stdout, so the worker's stderr is free to carry
      // JVM warnings and crash traces to the container log.
      .redirectError(ProcessBuilder.Redirect.INHERIT)
      .start()

  private def stackTrace(e: Throwable): String =
    val out = StringWriter()
    e.printStackTrace(PrintWriter(out))
    out.toString
