object Sqrt {

  
  def max(x: Int, y: Int): Int =
    if (x > y) x else y

  def sqrt(z: Int): Double =
    scala.math.sqrt(z.toDouble)

  val u: Int = ???
  sqrt(max(0,u))
}
