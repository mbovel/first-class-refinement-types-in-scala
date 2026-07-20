import stainless.lang._

object Foo {
  case class PosTuple(a: Int, b: Int)

  def test(): Unit = {
    val t = PosTuple(0, 1)
  }
}
