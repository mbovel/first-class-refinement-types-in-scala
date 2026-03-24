case class CheckedArray(size: Int):
  private val data = new Array[Double](size)
  def apply(i: Int): Double = data(i)
  def update(i: Int, x: Double): Unit = data(i) = x

def forRange(from: Int, to: Int)(body: Int => Unit): Unit =
  var i: Int = from
  while i < to do
    body(i)
    i = i + 1

case class Matrix(width: Int, height: Int):
  private val size = width * height
  private val data = CheckedArray(size)

  def index(i: Int, j: Int): Int =
    i * width + j

  def apply(i: Int, j: Int): Double =
    data(index(i, j))

  def update(i: Int, j: Int, x: Double): Unit =
    data(index(i, j)) = x

  def transpose(): Matrix =
    val res = Matrix(height, width)
    forRange(0, height): i =>
      forRange(0, width): j =>
        res(j, i) = this(i, j)
    res

  def mul(that: Matrix): Matrix =
    val res = Matrix(that.width, height)
    forRange(0, height): i =>
      forRange(0, that.width): j =>
        var sum = 0.0
        forRange(0, width): k =>
          sum = sum + this(i, k) * that(k, j)
        res(i, j) = sum
    res

def main =
  val m1 = Matrix(2, 3)
  val m2 = Matrix(3, 2)
  m1.mul(m2)

  val m1T = m1.transpose()
  m1T.mul(m1)
