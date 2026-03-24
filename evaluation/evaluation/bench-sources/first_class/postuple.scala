class PosTuple(val a: Int)(val b: Int with a + b > 0)

val t = PosTuple(0)(1)
