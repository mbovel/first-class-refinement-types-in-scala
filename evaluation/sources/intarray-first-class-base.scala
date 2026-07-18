object IntArray {


  case class IntArray(length: Int) {
    def access(i: Int): Unit =
      ()
  }

  def test(): Unit = {
    val a = new IntArray(3)
    a.access(1)
  }
}
