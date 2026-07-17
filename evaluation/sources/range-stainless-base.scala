

case class CheckedArray(val size: Int):
  private val data = new Array[Double](size)
  def apply(i: Int): Double = data(i)

case class RRange(from: Int, until: Int):
  inline def foreach(body: Int => Unit): Unit =
    var i: Int = from
    while i < until do
      body(i)
      i += 1

@main def checkedArrayTest(): Unit =
  val a = CheckedArray(10)
  val r = RRange(0, 10)
  for i <- r do
    a(i)
