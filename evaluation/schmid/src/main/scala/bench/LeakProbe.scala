package bench

import java.lang.management.ManagementFactory

import bench.compilers.SchmidCompiler

/** Diagnostic (not part of the benchmarks): compiles one source repeatedly
  * in-process and tracks retained heap, dumping jmap histograms early and
  * late so leaked classes show up as the delta. */
object LeakProbe {
  def main(args: Array[String]): Unit = {
    val source = if (args.length > 0) args(0) else "intarray"
    val iters = if (args.length > 1) args(1).toInt else 25
    val jmap = if (args.length > 2) args(2) else ""
    val pid = ManagementFactory.getRuntimeMXBean.getName.split("@")(0)
    println(s"probe pid=$pid source=$source iters=$iters")
    val rt = Runtime.getRuntime

    def usedMb: Long = {
      System.gc(); System.gc()
      (rt.totalMemory - rt.freeMemory) / (1024 * 1024)
    }

    def histo(tag: String): Unit = if (jmap.nonEmpty) {
      val f = new java.io.File(s"probe-histo-$source-$tag.txt")
      val pb = new ProcessBuilder(jmap, "-histo:live", pid)
      pb.redirectOutput(f)
      pb.redirectErrorStream(true)
      pb.start().waitFor()
      println(s"wrote ${f.getPath}")
    }

    var i = 1
    while (i <= iters) {
      new java.io.File("out-probe").mkdirs()
      val path = if (source.contains("/")) source else s"../sources/$source-schmid.scala"
      SchmidCompiler.compile(Seq(path), Seq("-nowarn") ++ args.drop(3), "out-probe")
      println(s"iter $i: used-after-gc = ${usedMb} MB")
      if (i == 5 || i == iters) histo(s"iter$i")
      i += 1
    }
  }
}
