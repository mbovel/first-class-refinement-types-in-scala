object IntArray {


  class IntArray(val length: Int) {
    def access(i: Int): Unit =
      ()
  }

  def test(): Unit = {
    val a = new IntArray(3)
    a.access(1)
  }
}
