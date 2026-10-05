// Override with e.g. -Ddotty.version=3.10.1-RC1-bin-SNAPSHOT -Ddotty.organization=org.scala-lang
// to run against a locally published compiler, as in evaluation/first-class.
val dottyVersion = sys.props.getOrElse("dotty.version", "3.10.1-RC1-bin-20260903-e1f9361-NIGHTLY")
val dottyOrganization = sys.props.getOrElse("dotty.organization", "ch.epfl.lara")

lazy val server = project
  .in(file("."))
  .enablePlugins(JavaAppPackaging)
  .settings(
    name := "playground-server",
    scalaVersion := dottyVersion,
    scalaOrganization := dottyOrganization,
    scalacOptions ++= Seq("-feature", "-Werror", "-deprecation"),
    libraryDependencies ++= Seq(
      "com.lihaoyi" %% "cask" % "0.11.0",
      dottyOrganization %% "scala3-compiler" % dottyVersion,
      dottyOrganization %% "scala3-library" % dottyVersion,
    ),
    // cask pulls org.scala-lang:scala3-library_3, which coursier cannot reconcile against
    // ch.epfl.lara:scala3-library_3 (different groupId, so no eviction). Without this, two
    // standard libraries end up on the classpath.
    excludeDependencies += ExclusionRule("org.scala-lang", "scala3-library_3"),
    // Fork so that java.class.path contains the full classpath, as Compile expects.
    fork := true,
    Compile / run / connectInput := true,
    javaOptions ++= Seq("-Xmx2g"),
  )
