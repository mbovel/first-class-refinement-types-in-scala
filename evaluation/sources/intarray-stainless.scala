case class IntArray(length: BigInt):
  require(length >= 0)

  def access(i: BigInt): Unit =
    require(i >= 0 && i < length)
    ()

def test(): Unit =
  val a = IntArray(3)
  a.access(1)
