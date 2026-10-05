package playground

import java.io.{DataInputStream, DataOutputStream}
import java.nio.charset.StandardCharsets

/** How [[Compile]] and the [[Worker]] it spawns talk over the worker's pipes.
 *
 *  Frames carry their length rather than ending at a delimiter, because both a snippet and
 *  a diagnostic can contain anything at all, newlines and NUL bytes included. A delimiter
 *  would need escaping; a length does not. This exists only because the worker outlives a
 *  single request: were it to exit after each one, end of stream would mark the end of the
 *  response and none of this would be needed.
 */
private[playground] object Framing:

  def write(out: DataOutputStream, text: String): Unit =
    val bytes = text.getBytes(StandardCharsets.UTF_8)
    out.writeInt(bytes.length)
    out.write(bytes)
    out.flush()

  /** Throws `EOFException` once the other end is gone, which is how both sides learn that
   *  the exchange is over.
   */
  def read(in: DataInputStream): String =
    val bytes = new Array[Byte](in.readInt())
    in.readFully(bytes)
    String(bytes, StandardCharsets.UTF_8)
