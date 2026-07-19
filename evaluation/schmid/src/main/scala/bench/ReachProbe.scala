package bench

import java.lang.reflect.{Field, Modifier}
import java.util.zip.ZipFile

import scala.collection.JavaConverters._
import scala.collection.mutable

import bench.compilers.SchmidCompiler

/** Diagnostic (not part of the benchmarks): compiles a source a few times,
  * then walks the heap by reflection from every Scala object singleton
  * (and thread-locals) and reports which roots reach more than one
  * ContextBase, i.e. retain previous runs' compiler universes. */
object ReachProbe {

  val ContextBaseClass = "dotty.tools.dotc.core.Contexts$ContextBase"

  def main(args: Array[String]): Unit = {
    val source = if (args.length > 0) args(0) else "intarray"
    val iters = if (args.length > 1) args(1).toInt else 4

    var i = 1
    while (i <= iters) {
      new java.io.File("out-probe").mkdirs()
      val path = if (source.contains("/")) source else s"../sources/$source-schmid.scala"
      SchmidCompiler.compile(Seq(path), Seq("-nowarn"), "out-probe")
      println(s"compiled iter $i")
      i += 1
    }
    System.gc(); System.gc()

    val roots = collectRoots()
    println(s"scanning ${roots.size} roots...")
    val results = roots.flatMap { case (name, obj) =>
      val (visited, nBases) = countReachableContextBases(obj)
      if (nBases > 0) Some((name, visited, nBases)) else None
    }
    println(f"${"root"}%-70s ${"visited"}%10s ${"ContextBases"}%12s")
    for ((name, visited, nBases) <- results.sortBy(-_._3))
      println(f"$name%-70s $visited%10d $nBases%12d")
  }

  /** All initialized Scala object singletons on the classpath in the
    * interesting packages, plus all threads' thread-local values. */
  def collectRoots(): Seq[(String, AnyRef)] = {
    val out = mutable.ArrayBuffer[(String, AnyRef)]()
    val prefixes = Seq("dotty/", "leon/", "smtlib/", "scala/reflect/io/", "scala/tools/nsc/")
    val cp = System.getProperty("java.class.path").split(java.io.File.pathSeparatorChar)
    for (entry <- cp if entry.endsWith(".jar")) {
      val zf = try new ZipFile(entry) catch { case _: Exception => null }
      if (zf != null) {
        for (ze <- zf.entries().asScala) {
          val n = ze.getName
          if (n.endsWith("$.class") && !n.contains("$$anon") && prefixes.exists(n.startsWith)) {
            val clsName = n.stripSuffix(".class").replace('/', '.')
            try {
              val cls = Class.forName(clsName, false, getClass.getClassLoader)
              val f = cls.getDeclaredField("MODULE$")
              f.setAccessible(true)
              val v = f.get(null) // may force initialization; fine for diagnosis
              if (v != null) out += ((clsName, v))
            } catch { case _: Throwable => }
          }
        }
        zf.close()
      }
    }
    for (t <- Thread.getAllStackTraces.keySet().asScala) {
      try {
        val f = classOf[Thread].getDeclaredField("threadLocals")
        f.setAccessible(true)
        val map = f.get(t)
        if (map != null) {
          val tableF = map.getClass.getDeclaredField("table")
          tableF.setAccessible(true)
          val table = tableF.get(map).asInstanceOf[Array[AnyRef]]
          if (table != null) for ((e, idx) <- table.zipWithIndex if e != null) {
            val vf = e.getClass.getDeclaredField("value")
            vf.setAccessible(true)
            val v = vf.get(e)
            if (v != null) out += ((s"threadlocal:${t.getName}#$idx:${v.getClass.getName}", v))
          }
        }
      } catch { case _: Throwable => }
    }
    out
  }

  val fieldCache = new java.util.HashMap[Class[_], Array[Field]]()

  def fieldsOf(cls: Class[_]): Array[Field] = {
    var fs = fieldCache.get(cls)
    if (fs == null) {
      val buf = mutable.ArrayBuffer[Field]()
      var c = cls
      while (c != null) {
        for (f <- c.getDeclaredFields
             if !Modifier.isStatic(f.getModifiers) && !f.getType.isPrimitive) {
          try { f.setAccessible(true); buf += f } catch { case _: Throwable => }
        }
        c = c.getSuperclass
      }
      fs = buf.toArray
      fieldCache.put(cls, fs)
    }
    fs
  }

  def skip(o: AnyRef): Boolean = o match {
    case _: Class[_] | _: ClassLoader | _: Thread | _: java.lang.ref.Reference[_] => true
    case _ => false
  }

  /** BFS over instance fields; returns (#objects visited, #ContextBases seen). */
  def countReachableContextBases(root: AnyRef): (Int, Int) = {
    val visited = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap[AnyRef, java.lang.Boolean]())
    val queue = new java.util.ArrayDeque[AnyRef]()
    var nBases = 0
    queue.add(root); visited.add(root)
    while (!queue.isEmpty && visited.size < 30000000) {
      val o = queue.poll()
      if (o.getClass.getName == ContextBaseClass) nBases += 1
      if (o.getClass.isArray) {
        if (!o.getClass.getComponentType.isPrimitive)
          for (e <- o.asInstanceOf[Array[AnyRef]] if e != null && !skip(e) && visited.add(e))
            queue.add(e)
      } else {
        for (f <- fieldsOf(o.getClass)) {
          val v = try f.get(o) catch { case _: Throwable => null }
          if (v != null && !skip(v) && visited.add(v)) queue.add(v)
        }
      }
    }
    (visited.size, nBases)
  }
}
