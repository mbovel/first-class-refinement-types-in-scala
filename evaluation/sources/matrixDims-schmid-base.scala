object Foo {
  class Matrix(val width: Int, val height: Int) {
    def transpose(): Matrix =
      new Matrix(height, width)

    def mul(that: Matrix): Matrix =
      new Matrix(that.width, height)
  }
  val m1 = new Matrix(2, 3)
  val m2 = new Matrix(3, 2)
  m1.mul(m2)
  val m1T = m1.transpose()
  m1T.mul(m1)
}
