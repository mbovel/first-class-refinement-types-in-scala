// `stage` lays the app out as bin/ + lib/ with one jar per dependency, which keeps
// java.class.path readable by Compile's stdlib filter. A fat jar would not.
addSbtPlugin("com.github.sbt" % "sbt-native-packager" % "1.12.0")
