package playground

import java.nio.charset.StandardCharsets
import scala.util.matching.Regex

/** The whole of `https://icvm0175.epfl.ch`: POST a snippet to `/`, get the compiler's
 *  output back as text. The playground page itself lives on the project website.
 */
object Server extends cask.MainRoutes:

  /** The reverse proxy reaches this over the container network, so bind every interface. */
  override def host: String = sys.env.getOrElse("PLAYGROUND_HOST", "0.0.0.0")
  override def port: Int = sys.env.get("PLAYGROUND_PORT").fold(8080)(_.toInt)

  /** Where the playground page is served from. */
  private val allowedOrigins = Set("https://matt.bovel.net")

  /** Also allowed, so that the page can be developed against this backend. */
  private val localOrigin: Regex = """^http://(?:localhost|127\.0\.0\.1)(?::\d+)?$""".r

  /** Only one origin can be returned, so echo back the request's when it is one we allow.
   *  cask lowercases incoming header names.
   */
  private def cors(request: cask.Request): Seq[(String, String)] =
    val origin = request.headers.get("origin").flatMap(_.headOption)
    val allowed = origin.filter(o => allowedOrigins(o) || localOrigin.matches(o))
    allowed.toSeq.map("Access-Control-Allow-Origin" -> _) ++ Seq(
      "Access-Control-Allow-Methods" -> "POST, OPTIONS",
      "Access-Control-Allow-Headers" -> "Content-Type",
      // The response varies by request origin, so caches must not share it across origins.
      "Vary" -> "Origin",
    )

  private val plainText = "Content-Type" -> "text/plain; charset=utf-8"

  /** Snippets are small. nginx rejects larger bodies before they reach us. */
  private val maxBodySize = 64 * 1024

  @cask.get("/")
  def usage(request: cask.Request) =
    cask.Response("POST Scala source here to compile it.\n", headers = cors(request) :+ plainText)

  /** Diagnostics are a normal result, not an HTTP error, so that the client can tell them
   *  apart from a transport failure.
   */
  @cask.post("/")
  def compile(request: cask.Request) =
    val headers = cors(request) :+ plainText
    val body = request.bytes
    if body.length > maxBodySize then
      cask.Response(s"Source too large: ${body.length} bytes, the limit is $maxBodySize.\n", 413, headers)
    else
      Compile(String(body, StandardCharsets.UTF_8)) match
        case Compile.Result.Output(text) => cask.Response(text, 200, headers)
        case Compile.Result.TimedOut => cask.Response("Compilation timed out.\n", 503, headers)

  @cask.options("/")
  def preflight(request: cask.Request) =
    cask.Response("", headers = cors(request) :+ ("Access-Control-Max-Age" -> "86400"))

  Compile.warmUp()
  initialize()
