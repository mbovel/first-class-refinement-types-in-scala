package bench

class SchmidBaseBenchmarks extends SchmidBenchmarks {
  override def suffix = "schmid-base"
  override def extraOptions = Seq("-Yskip:liquidtyper")
}
