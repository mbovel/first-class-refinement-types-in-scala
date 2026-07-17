object Foo {
  type NonNeg = Int
  val MAX_INT = 2147483647
  def f(x: NonNeg): NonNeg => NonNeg = {
    def g(y: NonNeg): NonNeg = if (x + y >= 0) x + y else MAX_INT
    g(_)
  }
}
