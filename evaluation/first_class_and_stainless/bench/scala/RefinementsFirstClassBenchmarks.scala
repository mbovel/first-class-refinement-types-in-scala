package bench

import bench.compilers.DottyCompiler
import org.openjdk.jmh.annotations.{Benchmark, Warmup}

class RefinementsFirstClassBenchmarks extends RefinementsBenchmarks:

  override def sourcesDir = BenchSources.dir + "/first_class"

  override def options = Seq("-language:experimental.qualifiedTypes")
