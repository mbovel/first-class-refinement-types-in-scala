object Foo {
  class PosTuple(val a: Int)(val b: {v: Int with a + v > 0})
  val t = new PosTuple(0)(1)
}
