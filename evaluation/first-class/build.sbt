val sharedScalacOptions = Seq("-feature", "-Werror", "-deprecation")

val dottyVersion = "3.8.4-RC1-bin-20260316-3082482-NIGHTLY"

scalaVersion := dottyVersion
scalaOrganization := "ch.epfl.lara"

lazy val bench =
  project
    .in(file("bench"))
    .dependsOn()
    .settings(
      scalaVersion := dottyVersion,
      scalaOrganization := "ch.epfl.lara",
      scalacOptions ++= sharedScalacOptions,
      libraryDependencies ++= Seq(
        "ch.epfl.lara" %% "scala3-compiler" % dottyVersion,
        "ch.epfl.lara" %% "scala3-library" % dottyVersion,
      ),
      Compile / scalaSource := baseDirectory.value / "scala",
      // Fork so that java.class.path contains the full classpath, as DottyCompiler expects
      // (JMH already forks; this covers `bench/runMain`).
      Compile / run / fork := true,
    )
    .enablePlugins(JmhPlugin)
