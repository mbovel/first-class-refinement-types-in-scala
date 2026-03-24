object Foo {
  val MAX_INT = 2147483647
  def f(x: Int): Int => Int = {
    def g(y: Int): Int = if (x + y > 0) x + y else MAX_INT
    g(_)
  }
}
