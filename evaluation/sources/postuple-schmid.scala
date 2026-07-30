object Foo {
  class PosTuple(val a: Int)(val b: {v: Int if a + v > 0})
  val t = new PosTuple(0)(1)
}
