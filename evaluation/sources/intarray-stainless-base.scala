type NonNeg = Int

class IntArray(val length: NonNeg, init: Int):
  private val data = Array.fill(length)(init)

  def access(i: NonNeg): Int =
    data(i)

val a = IntArray(3, 0)
val r = a.access(1)
