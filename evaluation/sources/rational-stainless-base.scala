import stainless.lang._

object Foo {
  case class Rational(p: Int, q: Int) {
    val asFloat = p / q
  }

  def test(): Unit = {
    val r = Rational(1, 2).asFloat
  }
}
