package bench

import java.util.concurrent.TimeUnit.MILLISECONDS

import org.openjdk.jmh.annotations.{
  BenchmarkMode,
  Fork,
  Level,
  Measurement,
  OutputTimeUnit,
  Scope,
  Setup,
  State,
  Warmup
}

@Fork(
  value = 1,
  jvmArgsPrepend = Array("-XX:+PrintCommandLineFlags", "-Xms8G", "-Xmx8G")
)
@Warmup(iterations = 180)
@Measurement(iterations = 40)
@BenchmarkMode(Array(org.openjdk.jmh.annotations.Mode.SingleShotTime))
@State(Scope.Benchmark)
@OutputTimeUnit(MILLISECONDS)
abstract class CompilationBenchmarks {

  val outDir = "out"

  @Setup(Level.Iteration)
  def setup(): Unit = {
    removeAndCreateDir(outDir)
  }

  def removeAndCreateDir(dir: String): Unit = {
    import scala.sys.process._
    s"rm -rf $dir".!
    s"mkdir -p $dir".!
  }
}
