package playground

import java.io.{
  BufferedInputStream, BufferedOutputStream, DataInputStream, DataOutputStream, EOFException,
  FileDescriptor, FileOutputStream, PrintStream,
}

/** The child process: reads snippets on stdin, writes compiler output on stdout, until the
 *  parent closes the pipe or kills it. See [[Compile]] for why compilation happens here.
 */
object Worker:

  def main(args: Array[String]): Unit =
    // Take the real stdout for the protocol before anything else can write to it, then
    // point System.out at stderr. The compiler and the libraries it loads do print, and a
    // stray line on stdout would desynchronise the framing.
    val responses = DataOutputStream(BufferedOutputStream(FileOutputStream(FileDescriptor.out)))
    System.setOut(PrintStream(FileOutputStream(FileDescriptor.err), true))
    val requests = DataInputStream(BufferedInputStream(System.in))

    // The typer recurses deeply, far past what a default stack allows.
    val thread = Thread
      .ofPlatform()
      .name("dotc")
      .stackSize(32L * 1024 * 1024)
      .unstarted: () =>
        try
          while true do Framing.write(responses, Dotc.compile(Framing.read(requests)))
        catch case _: EOFException => () // the parent is done with us

    thread.start()
    thread.join()
