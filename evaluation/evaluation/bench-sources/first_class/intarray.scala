type NonNeg = {v: Int with v >= 0}

case class IntArray(length: NonNeg):


  def access(i: NonNeg with i < length): Unit =
    ()


def test(): Unit =
  val a = IntArray(3)
  a.access(1)
