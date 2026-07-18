object Sqrt {
  type NonNeg = {v: Int if v >= 0}

  def max(x: Int, y: Int): {v: Int if v >= x && v >= y} =
    if (x > y) x else y

  def sqrt(z: NonNeg): Double =
    scala.math.sqrt(z.toDouble)

  val u: Int = ???
  sqrt(max(0, u))
}
