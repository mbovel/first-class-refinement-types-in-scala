// JDK 8 home: $JDK8_HOME if set, otherwise resolved with coursier.
lazy val jdk8Home: Option[File] = {
  val fromEnv = sys.env.get("JDK8_HOME")
  def fromCoursier = scala.util
    .Try(scala.sys.process.Process(Seq("cs", "java-home", "--jvm", "temurin:8")).!!.trim)
    .toOption
  val home = fromEnv.orElse(fromCoursier).map(file(_))
  if (home.isEmpty)
    println("[warn] JDK 8 not found (set JDK8_HOME or install coursier); benchmarks will run on the default JVM")
  home
}

lazy val bench = project
  .in(file("."))
  .settings(
    scalaVersion := "2.11.5",
    scalacOptions ++= Seq("-feature", "-deprecation"),
    // The benchmark JVMs run on JDK 8; make javac output (JMH generated
    // sources) run there.
    javacOptions ++= Seq("--release", "8"),
    libraryDependencies ++= Seq(
      // Managed dependencies of the refined-dotty build (see its project/Build.scala)
      "me.d-d" % "scala-compiler" % "2.11.5-20160322-171045-e19b30b3cd",
      "jline" % "jline" % "2.12",
      "org.scala-lang.modules" %% "scala-xml" % "1.0.1",
    ),
    // refined-dotty, Leon, and scala-smtlib jars, built by setup.sh
    Compile / unmanagedJars ++= (baseDirectory.value / "lib" ** "*.jar").classpath,
    // Run the JMH harness on JDK 8 (JMH then forks the benchmark JVMs with
    // the same JVM), so that the 2016 compiler runs on the JDK of its time.
    Jmh / run / fork := true,
    Jmh / run / javaHome := jdk8Home,
  )
  .enablePlugins(JmhPlugin)
