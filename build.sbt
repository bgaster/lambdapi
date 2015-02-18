lazy val root = (project in file(".")).
  settings(
    name              := "lambdapi",
    version           := "1.0",
    scalaVersion      := "2.11.5",
    organization      := "com.github.bendict.gaster",
    mainClass in assembly := Some("com.example.Main")
  )

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.3"
libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.8.0"
