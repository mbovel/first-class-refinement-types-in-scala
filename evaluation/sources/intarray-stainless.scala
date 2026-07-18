import stainless.lang._

object IntArray {

  case class IntArray(length: Int) {
    require(length >= 0)

    def access(i: Int): Unit = {
      require(0 <= i && i < length)
      ()
    }
  }

  def test(): Unit = {
    val a = new IntArray(3)
    a.access(1)
  }
}
