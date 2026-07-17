

trait CheckedArray[T]:
  def size: Int
  def apply(i: Int): T

case class CheckedRange(from: Int, until: Int):
  def foreach(body: (x: Int) => Unit): Unit =
    foreachLoop(from, body)

  @annotation.tailrec
  private def foreachLoop(
    x: Int,
    body: (x: Int) => Unit
  ): Unit =
    body(x)
    val next = x + 1
    if from <= next && next < until then foreachLoop(next, body)

def checkedArrayTest[T](a: CheckedArray[T]): Unit =
  val r = CheckedRange(0, 10)
  for i <- r do
    a(i)
