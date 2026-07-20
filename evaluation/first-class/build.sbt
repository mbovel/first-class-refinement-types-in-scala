val sharedScalacOptions = Seq("-feature", "-Werror", "-deprecation")

// Override with e.g. -Ddotty.version=3.10.0-RC1-bin-SNAPSHOT -Ddotty.organization=org.scala-lang
// to benchmark a locally published compiler (sbt clean community-build/prepareCommunityBuild).
val dottyVersion = sys.props.getOrElse("dotty.version", "3.10.0-RC1-bin-20260720-5f1bae1-NIGHTLY")
val dottyOrganization = sys.props.getOrElse("dotty.organization", "ch.epfl.lara")

scalaVersion := dottyVersion
scalaOrganization := dottyOrganization

lazy val bench =
  project
    .in(file("bench"))
    .dependsOn()
    .settings(
      scalaVersion := dottyVersion,
      scalaOrganization := dottyOrganization,
      scalacOptions ++= sharedScalacOptions,
      libraryDependencies ++= Seq(
        dottyOrganization %% "scala3-compiler" % dottyVersion,
        dottyOrganization %% "scala3-library" % dottyVersion,
      ),
      Compile / scalaSource := baseDirectory.value / "scala",
      // Fork so that java.class.path contains the full classpath, as DottyCompiler expects
      // (JMH already forks; this covers `bench/runMain`).
      Compile / run / fork := true,
    )
    .enablePlugins(JmhPlugin)
