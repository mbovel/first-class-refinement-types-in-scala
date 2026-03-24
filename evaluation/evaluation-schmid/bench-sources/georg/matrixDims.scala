object Foo {
  type Pos = { v: Int if v >= 0 }
  class Matrix(val width: Pos, val height: Pos) {
    def mul(thatHeight: { v: Int if v == this.width }, thatWidth: Pos): Unit = ()
  }
  val m1 = new Matrix(2, 3)
  m1.mul(2, 3)
}
