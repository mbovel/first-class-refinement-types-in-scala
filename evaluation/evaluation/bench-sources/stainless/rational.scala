import stainless.lang._

object RationalBench:

  case class Rational(p: BigInt, q: BigInt):
    require(q != 0)

  def test(): Unit = {
    val r = Rational(BigInt(1), BigInt(2))
  }
