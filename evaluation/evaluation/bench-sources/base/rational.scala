class Rational(p: Int, q: Int):
  val asFloat = p / q

val r = Rational(1, 2).asFloat
