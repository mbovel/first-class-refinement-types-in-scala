import stainless.lang._

object Sqrt {

  def max(x: Int, y: Int): Int = {
    if (x > y) x else y
  }.ensuring(v => v >= x && v >= y)

  def sqrt(z: Int): Int = {
    require(z >= 0)
    z
  }

  def test(u: Int): Int =
    sqrt(max(0, u))
}
