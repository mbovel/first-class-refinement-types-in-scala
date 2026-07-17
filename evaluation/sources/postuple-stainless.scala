import stainless.lang._

object PosTupleBench:

  case class PosTuple(a: BigInt, b: BigInt):
    require(a + b > 0)

  def test(): Unit = {
    val t = PosTuple(BigInt(0), BigInt(1))
  }
