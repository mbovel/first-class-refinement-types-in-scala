package bench

import bench.compilers.DottyCompiler
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

class RefinementsBaseBenchmarks extends RefinementsBenchmarks:

  override def suffix = "first-class-base"

  override def options = Seq()
