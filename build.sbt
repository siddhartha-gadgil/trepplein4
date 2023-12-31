name := "trepplein"
description := "Independent type-checker for the dependently typed theorem prover Lean"
homepage := Some(url("https://github.com/gebner/trepplein"))
startYear := Some(2017)
licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))
// maintainer := "gebner@gebner.org"

version := "1.1"

scalaVersion := "2.13.12"

libraryDependencies += "com.github.scopt" %% "scopt" % "4.1.0"
libraryDependencies += "org.specs2" %% "specs2-core" % "4.20.2" % "test"

scalacOptions ++= Seq("-opt:l:inline", "-opt-inline-from:**", "-opt-warnings", "-deprecation")


enablePlugins(JavaAppPackaging)
javaOptions in Universal ++= Seq("-J-Xss30m")

import scalariform.formatter.preferences._
import com.typesafe.sbt.SbtScalariform.ScalariformKeys
ScalariformKeys.preferences := ScalariformKeys.preferences.value
  .setPreference(DoubleIndentConstructorArguments, true)


libraryDependencies += {
  "com.lihaoyi" % "ammonite" % "2.5.11" % "test" cross CrossVersion.full
}

sourceGenerators in Test += Def.task {
  val file = (sourceManaged in Test).value / "amm.scala"
  IO.write(file, """object amm extends App { ammonite.AmmoniteMain.main(args) }""")
  Seq(file)
}.taskValue
