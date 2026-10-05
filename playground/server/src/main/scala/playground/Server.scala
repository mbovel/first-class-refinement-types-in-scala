package playground

import java.nio.charset.StandardCharsets

/** The whole of `https://icvm0175.epfl.ch`: POST a snippet to `/`, get the compiler's
 *  output back as text. The playground page itself lives on the project website.
 */
object Server extends cask.MainRoutes:

  /** The reverse proxy reaches this over the container network, so bind every interface. */
  override def host: String = sys.env.getOrElse("PLAYGROUND_HOST", "0.0.0.0")
  override def port: Int = sys.env.get("PLAYGROUND_PORT").fold(8080)(_.toInt)

  /** The page posting here is served from the project website, a different origin. */
  private val cors = Seq(
    "Access-Control-Allow-Origin" -> "https://matt.bovel.net",
    "Access-Control-Allow-Methods" -> "POST, OPTIONS",
    "Access-Control-Allow-Headers" -> "Content-Type",
  )

  private val plainText = "Content-Type" -> "text/plain; charset=utf-8"

  /** Snippets are small. nginx rejects larger bodies before they reach us. */
  private val maxBodySize = 64 * 1024

  @cask.get("/")
  def usage() =
    cask.Response("POST Scala source here to compile it.\n", headers = Seq(plainText))

  /** Diagnostics are a normal result, not an HTTP error, so that the client can tell them
   *  apart from a transport failure.
   */
  @cask.post("/")
  def compile(request: cask.Request) =
    val body = request.bytes
    if body.length > maxBodySize then
      cask.Response(s"Source too large: ${body.length} bytes, the limit is $maxBodySize.\n", 413, cors :+ plainText)
    else
      Compile(String(body, StandardCharsets.UTF_8)) match
        case Compile.Result.Output(text) => cask.Response(text, 200, cors :+ plainText)
        case Compile.Result.TimedOut => cask.Response("Compilation timed out.\n", 503, cors :+ plainText)

  @cask.options("/")
  def preflight() =
    cask.Response("", headers = cors :+ ("Access-Control-Max-Age" -> "86400"))

  initialize()
