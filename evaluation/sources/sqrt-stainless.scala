import stainless.lang._
import stainless.annotation._

object Sqrt {

  def max(x: Int, y: Int): Int = {
    if (x > y) x else y
  }.ensuring(v => v >= x && v >= y)

  @extern
  def sqrt(z: Int): Double = {
    require(z >= 0)
    scala.math.sqrt(z.toDouble)
  }

  def test(u: Int): Double =
    sqrt(max(0, u))
}
