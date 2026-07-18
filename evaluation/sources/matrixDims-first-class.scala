object Foo {
  type Pos = { v: Int with v >= 0 }

  case class Matrix(width: Pos, height: Pos)

  def transpose(m: Matrix): { v: Matrix with v.width == m.height && v.height == m.width } =
    new Matrix(m.height, m.width)

  def mul(m: Matrix)(that: { v: Matrix with v.height == m.width }): { v: Matrix with v.width == that.width && v.height == m.height } =
    new Matrix(that.width, m.height)

  def testMul(m1: { v: Matrix with v.width == 2 && v.height == 3 },
              m2: { v: Matrix with v.width == 3 && v.height == 2 }): { v: Matrix with v.width == 3 && v.height == 3 } =
    mul(m1)(m2)

  def testTranspose(m1: { v: Matrix with v.width == 2 && v.height == 3 }): { v: Matrix with v.width == 3 && v.height == 2 } =
    transpose(m1)
}
