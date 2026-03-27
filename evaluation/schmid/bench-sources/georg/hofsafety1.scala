object Foo {
  type NonNeg = { v: Int if v >= 0 }
  def g(f: NonNeg => Int): Int = f(0)
  g((x: NonNeg) => x)
}
