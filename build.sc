import mill._, scalalib._

object prolog extends RootModule with ScalaModule {
  def scalaVersion = "3.3.1"

  def scalacOptions = Seq(
    "-Yexplicit-nulls",
    "-Ysafe-init"
  )

  def ivyDeps = Agg(
    ivy"com.lihaoyi::pprint:0.8.1",
    ivy"org.parboiled::parboiled:2.5.0"
  )

  object test extends ScalaTests with TestModule.Utest {
    def ivyDeps = Agg(
      ivy"com.lihaoyi::utest:0.8.1"
    )
  }

}
