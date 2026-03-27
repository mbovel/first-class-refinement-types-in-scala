package bench

class GeorgRefinementBenchmarks extends GeorgBenchmarks {
  override def sourcesDir = "bench-sources/georg"
  override def extraOptions: Seq[String] = Seq.empty
}
