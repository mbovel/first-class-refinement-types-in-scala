package playground

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, StandardCopyOption}
import java.security.MessageDigest
import java.time.Instant
import java.time.temporal.ChronoUnit
import scala.jdk.StreamConverters.*
import scala.util.control.NonFatal

/** Every submitted program, kept on disk under the hash of what was compiled, with the
 *  compiler's output beside it.
 *
 *  It does two jobs at once. Identical submissions are answered from here rather than
 *  recompiled, which is worth more than it sounds: most visitors press Compile on the
 *  unmodified example, so a handful of entries cover much of the traffic. And what people
 *  try is worth keeping for a prototype whose point is to learn how the feature reads.
 *
 *  The hash covers the compiler version and its flags as well as the source, so a redeploy
 *  onto a newer compiler cannot serve diagnostics that compiler would not produce. A bucket
 *  holds numbered entries rather than one file, so that two programs that happened to hash
 *  alike both get stored instead of one shadowing the other; the stored input is compared
 *  before an entry is served.
 */
object Store:

  /** Without a directory configured the store is simply off, which is how a local run
   *  leaves nothing behind.
   */
  private val root: Option[Path] =
    sys.env.get("PLAYGROUND_STORE").map(Path.of(_)).flatMap: path =>
      try
        Files.createDirectories(path)
        Some(path)
      catch
        case NonFatal(e) =>
          System.err.println(s"playground: store at $path unusable, carrying on without it: $e")
          None

  /** Stop writing this far from a full filesystem. The endpoint is public, and filling the
   *  disk would take the whole machine down, not just this service.
   */
  private val reserve = 1024L * 1024 * 1024

  /** What the output depends on besides the source itself. NUL-joined so that no flag can
   *  be confused with the one next to it.
   */
  private val compiler =
    (dotty.tools.dotc.config.Properties.simpleVersionString +: Dotc.options).mkString("\u0000")

  /** The same thing, written into each entry so the corpus reads without this code. */
  private val description =
    (dotty.tools.dotc.config.Properties.simpleVersionString +: Dotc.options).mkString(" ")

  def get(source: String): Option[String] =
    try
      for
        base <- root
        entry <- entries(bucket(base, digest(source))).find(holds(_, source))
        output <- read(entry.resolve(OutputFile))
      yield output
    catch case NonFatal(_) => None

  def put(source: String, output: String): Unit =
    for base <- root do
      try
        val dir = bucket(base, digest(source))
        val existing = entries(dir)
        if !existing.exists(holds(_, source))
          && Files.getFileStore(base).getUsableSpace > reserve
        then
          Files.createDirectories(dir)
          write(dir, nextIndex(existing), source, output)
      catch
        case NonFatal(e) => System.err.println(s"playground: could not store a submission: $e")

  private val InputFile = "input.scala"
  private val OutputFile = "output.txt"
  private val VersionFile = "version"
  private val CreatedFile = "created"

  private def digest(source: String): String =
    val md = MessageDigest.getInstance("SHA-256")
    md.update(compiler.getBytes(StandardCharsets.UTF_8))
    md.update(0.toByte) // so that the compiler key and the source cannot run together
    md.update(source.getBytes(StandardCharsets.UTF_8))
    md.digest.map(b => f"$b%02x").mkString

  /** One level of sharding: a single directory holding every bucket gets slow to walk. */
  private def bucket(base: Path, hash: String): Path =
    base.resolve(hash.take(2)).resolve(hash)

  /** Numbered entries only, which skips the staging directories a concurrent write leaves. */
  private def entries(dir: Path): List[Path] =
    if !Files.isDirectory(dir) then Nil
    else
      val listing = Files.list(dir)
      try listing.toScala(List).filter(p => p.getFileName.toString.forall(_.isDigit))
      finally listing.close()

  private def nextIndex(existing: List[Path]): Int =
    existing.map(_.getFileName.toString.toInt).maxOption.fold(0)(_ + 1)

  private def holds(entry: Path, source: String): Boolean =
    read(entry.resolve(InputFile)).contains(source)

  /** Built aside and moved into place, so that a reader never sees half an entry. */
  private def write(dir: Path, index: Int, source: String, output: String): Unit =
    val staging = Files.createTempDirectory(dir, ".staging")
    try
      Files.writeString(staging.resolve(InputFile), source, StandardCharsets.UTF_8)
      Files.writeString(staging.resolve(OutputFile), output, StandardCharsets.UTF_8)
      // Both are implied by the bucket the entry sits in, but an entry that says what
      // produced it and when can be read on its own, which is the point of keeping them.
      Files.writeString(staging.resolve(VersionFile), s"$description\n", StandardCharsets.UTF_8)
      Files.writeString(
        staging.resolve(CreatedFile),
        s"${Instant.now.truncatedTo(ChronoUnit.SECONDS)}\n",
        StandardCharsets.UTF_8,
      )
      Files.move(staging, dir.resolve(index.toString), StandardCopyOption.ATOMIC_MOVE)
      ()
    catch
      case NonFatal(e) =>
        discard(staging)
        throw e

  private def discard(dir: Path): Unit =
    try
      val listing = Files.list(dir)
      try listing.forEach(p => { Files.deleteIfExists(p); () })
      finally listing.close()
      Files.deleteIfExists(dir)
      ()
    catch case NonFatal(_) => ()

  private def read(file: Path): Option[String] =
    try Some(Files.readString(file, StandardCharsets.UTF_8))
    catch case NonFatal(_) => None
