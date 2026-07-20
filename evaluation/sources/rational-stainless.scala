import stainless.lang._

object Foo {
  case class Rational(p: Int, q: Int) {
    require(q != 0)
    val asFloat = p / q
  }

  def test(): Unit = {
    val r = Rational(1, 2).asFloat
  }
}
