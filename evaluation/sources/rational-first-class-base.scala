object Foo {
  class Rational(p: Int, q: Int) {
    val asFloat = p / q
  }
  new Rational(1, 2).asFloat
}
