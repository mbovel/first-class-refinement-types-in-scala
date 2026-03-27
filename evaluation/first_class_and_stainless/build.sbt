val sharedScalacOptions = Seq("-feature", "-Werror", "-deprecation")

val dottyVersion = "3.8.4-RC1-bin-20260316-3082482-NIGHTLY"

scalaVersion := dottyVersion
scalaOrganization := "ch.epfl.lara"

// Stainless jars, built by setup.sh
val stainlessAssemblyJar = file("lib/stainless-assembly.jar")
val stainlessLibraryJar = file("lib/stainless-library.jar")

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
      Compile / unmanagedJars ++= Seq(
        Attributed.blank(stainlessAssemblyJar),
        Attributed.blank(stainlessLibraryJar),
      ),
      Compile / scalaSource := baseDirectory.value / "scala",
    )
    .enablePlugins(JmhPlugin)
