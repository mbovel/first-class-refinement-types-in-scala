val sharedScalacOptions = Seq("-feature", "-Werror", "-deprecation")

val dottyVersion = "3.7.2"

scalaVersion := dottyVersion

// Stainless jars, built by setup.sh
val stainlessAssemblyJar = file("lib/stainless-assembly.jar")
val stainlessLibraryJar = file("lib/stainless-library.jar")

lazy val bench =
  project
    .in(file("bench"))
    .dependsOn()
    .settings(
      scalaVersion := dottyVersion,
      scalacOptions ++= sharedScalacOptions,
      libraryDependencies ++= Seq(
        "org.scala-lang" %% "scala3-compiler" % dottyVersion,
        "org.scala-lang" %% "scala3-library" % dottyVersion,
      ),
      Compile / unmanagedJars ++= Seq(
        Attributed.blank(stainlessAssemblyJar),
        Attributed.blank(stainlessLibraryJar),
      ),
      Compile / scalaSource := baseDirectory.value / "scala",
      // Fork so that java.class.path contains the full classpath, as StainlessCompiler expects
      // (JMH already forks; this covers `bench/runMain`).
      Compile / run / fork := true,
    )
    .enablePlugins(JmhPlugin)
