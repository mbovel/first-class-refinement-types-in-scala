object Foo {
  class Rational(p: Int, q: {v: Int with v != 0}) {
    val asFloat = p / q
  }
  new Rational(1, 2).asFloat
}
