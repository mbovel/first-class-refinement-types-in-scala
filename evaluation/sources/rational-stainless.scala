import stainless.lang._

object Foo {
  case class Rational(p: BigInt, q: BigInt) {
    require(q != 0)
    val asFloat = p / q
  }

  def test(): Unit = {
    val r = Rational(BigInt(1), BigInt(2)).asFloat
  }
}
