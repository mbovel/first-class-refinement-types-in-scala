import stainless.lang._

object Foo {
  case class PosTuple(a: BigInt, b: BigInt)

  def test(): Unit = {
    val t = PosTuple(BigInt(0), BigInt(1))
  }
}
