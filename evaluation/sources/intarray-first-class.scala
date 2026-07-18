object IntArray {
  type NonNeg = {v: Int with v >= 0}

  case class IntArray(length: NonNeg) {
    def access(i: {v: NonNeg with v < this.length}): Unit =
      ()
  }

  def test(): Unit = {
    val a = new IntArray(3)
    a.access(1)
  }
}
