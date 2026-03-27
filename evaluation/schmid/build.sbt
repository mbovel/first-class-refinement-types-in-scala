lazy val root = project
  .in(file("."))
  .settings(
    scalaVersion := "2.11.5",
    scalacOptions ++= Seq("-feature", "-deprecation"),
    libraryDependencies ++= Seq(
      ("ch.epfl.lamp" % "dotty_2.11" % "0.1-SNAPSHOT")
        .exclude("org.scala-sbt", "interface"),
      "ch.epfl.lamp" % "dotty-interfaces" % "0.1-SNAPSHOT"
    ),
    // Leon, scala-smtlib, and sbt-interface JARs
    Compile / unmanagedJars ++= (baseDirectory.value / "lib" ** "*.jar").classpath
  )
  .enablePlugins(JmhPlugin)
