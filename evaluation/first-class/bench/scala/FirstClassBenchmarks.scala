package bench

import bench.compilers.DottyCompiler
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

class FirstClassBenchmarks extends RefinementsBenchmarks:

  override def suffix = "first-class"

  override def options = Seq("-language:experimental.qualifiedTypes")
