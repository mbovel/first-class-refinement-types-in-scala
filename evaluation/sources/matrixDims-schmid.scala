// matrixDims in Georg's syntax, with the full dimension specifications for
// transpose and mul. LiquidTyper restrictions shape the program, and the
// first-class and Stainless variants mirror its structure: mul's precondition
// uses a curried parameter list (as in postuple), since qualifiers cannot
// refer to other parameters in the same list; method results cannot be
// refined inside a class, so transpose and mul are top-level functions;
// case classes crash the checker, so Matrix is a plain class; and
// refined-result calls only check in result position with parameters or
// literals as arguments, so each test is a separate function taking its
// inputs as refined parameters.
object Foo {
  type Pos = { v: Int if v >= 0 }

  class Matrix(val width: Pos, val height: Pos)

  def transpose(m: Matrix): { v: Matrix if v.width == m.height && v.height == m.width } =
    new Matrix(m.height, m.width)

  def mul(m: Matrix)(that: { v: Matrix if v.height == m.width }): { v: Matrix if v.width == that.width && v.height == m.height } =
    new Matrix(that.width, m.height)

  def testMul(m1: { v: Matrix if v.width == 2 && v.height == 3 },
              m2: { v: Matrix if v.width == 3 && v.height == 2 }): { v: Matrix if v.width == 3 && v.height == 3 } =
    mul(m1)(m2)

  def testTranspose(m1: { v: Matrix if v.width == 2 && v.height == 3 }): { v: Matrix if v.width == 3 && v.height == 2 } =
    transpose(m1)
}
