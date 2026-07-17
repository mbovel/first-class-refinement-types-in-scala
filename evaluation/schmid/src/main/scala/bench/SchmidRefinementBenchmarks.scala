package bench

class SchmidRefinementBenchmarks extends SchmidBenchmarks {
  override def suffix = "schmid"
  override def extraOptions: Seq[String] = Seq.empty
}
