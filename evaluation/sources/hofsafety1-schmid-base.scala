object Foo {
  def g(f: Int => Int): Int = f(0)
  g((x: Int) => x)
}
