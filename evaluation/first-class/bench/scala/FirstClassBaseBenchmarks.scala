package bench

import bench.compilers.DottyCompiler
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

class FirstClassBaseBenchmarks extends AbstractFirstClassBenchmarks:

  override def suffix = "first-class-base"

  override def options = Seq()
