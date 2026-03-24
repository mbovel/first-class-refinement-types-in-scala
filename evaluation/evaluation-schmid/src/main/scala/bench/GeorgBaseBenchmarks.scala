package bench

class GeorgBaseBenchmarks extends GeorgBenchmarks {
  override def sourcesDir = "bench-sources/georg_base"
  override def extraOptions = Seq("-Yskip:liquidtyper")
}
