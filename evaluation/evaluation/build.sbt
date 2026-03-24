val sharedScalacOptions = Seq("-feature", "-Werror", "-deprecation")

val dottyVersion = "3.8.4-RC1-bin-20260317-ab3d7ec-NIGHTLY"

scalaVersion := dottyVersion
scalaOrganization := "ch.epfl.lara"

// Path to the Stainless assembly jar (compiler plugin) and library jar
val stainlessAssemblyJar = file("stainless/frontends/dotty/target/scala-3.8.4-RC1-bin-20260317-ab3d7ec-NIGHTLY")
  .listFiles.toSeq.filter(_.getName.startsWith("stainless-dotty-assembly")).head
val stainlessLibraryJar = file("stainless/frontends/library/target/scala-3.8.4-RC1-bin-20260317-ab3d7ec-NIGHTLY")
  .listFiles.toSeq.filter(_.getName.startsWith("stainless-library")).head

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
