object Foo {


  class Matrix(val width: Int, val height: Int)

  def transpose(m: Matrix): Matrix =
    new Matrix(m.height, m.width)

  def mul(m: Matrix)(that: Matrix): Matrix =
    new Matrix(that.width, m.height)

  def testMul(m1: Matrix, m2: Matrix): Matrix =
    mul(m1)(m2)

  def testTranspose(m1: Matrix): Matrix =
    transpose(m1)
}
