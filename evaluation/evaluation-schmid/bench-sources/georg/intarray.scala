object IntArray {
  type NonNeg = {v: Int if v >= 0}

  class IntArray(val length: NonNeg) {
    def access(i: {v: NonNeg if v < this.length}): Unit =
      ()
  }

  def test(): Unit = {
    val a = new IntArray(3)
    a.access(1)
  }
}
