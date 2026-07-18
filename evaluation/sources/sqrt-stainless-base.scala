import stainless.lang._

object Sqrt {

  def max(x: Int, y: Int): Int = {
    if (x > y) x else y
  }

  def sqrt(z: Int): Int = {
    z
  }

  def test(u: Int): Int =
    sqrt(max(0, u))
}
