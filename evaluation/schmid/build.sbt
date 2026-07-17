lazy val root = project
  .in(file("."))
  .settings(
    scalaVersion := "2.11.5",
    scalacOptions ++= Seq("-feature", "-deprecation"),
    // Benchmarks fork a JDK 8 JVM (JMH -jvm option); make javac output (JMH
    // generated sources) run there.
    javacOptions ++= Seq("--release", "8"),
    libraryDependencies ++= Seq(
      // Managed dependencies of the refined-dotty build (see its project/Build.scala)
      "me.d-d" % "scala-compiler" % "2.11.5-20160322-171045-e19b30b3cd",
      "jline" % "jline" % "2.12",
      "org.scala-lang.modules" %% "scala-xml" % "1.0.1",
    ),
    // refined-dotty, Leon, and scala-smtlib jars, built by setup.sh
    Compile / unmanagedJars ++= (baseDirectory.value / "lib" ** "*.jar").classpath
  )
  .enablePlugins(JmhPlugin)
