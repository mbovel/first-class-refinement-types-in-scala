import stainless.lang._

object Foo {
  case class Matrix(width: Int, height: Int) {
    require(width >= 0 && height >= 0)
  }

  def transpose(m: Matrix): Matrix = {
    new Matrix(m.height, m.width)
  }.ensuring(v => v.width == m.height && v.height == m.width)

  def mul(m: Matrix)(that: Matrix): Matrix = {
    require(that.height == m.width)
    new Matrix(that.width, m.height)
  }.ensuring(v => v.width == that.width && v.height == m.height)

  def testMul(m1: Matrix, m2: Matrix): Matrix = {
    require(m1.width == 2 && m1.height == 3 && m2.width == 3 && m2.height == 2)
    mul(m1)(m2)
  }.ensuring(v => v.width == 3 && v.height == 3)

  def testTranspose(m1: Matrix): Matrix = {
    require(m1.width == 2 && m1.height == 3)
    transpose(m1)
  }.ensuring(v => v.width == 3 && v.height == 2)
}
