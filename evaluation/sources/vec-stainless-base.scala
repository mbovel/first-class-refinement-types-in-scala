import stainless.lang._

trait Vec[T]:
  def len: Int

  def concat(b: Vec[T]): Vec[T] = {
    (??? : Vec[T])
  }

  def zip[S](b: Vec[S]): Vec[(T, S)] = {
    (??? : Vec[(T, S)])
  }

def example3(
  n: Int,
  m: Int,
  v1: Vec[Int],
  v2: Vec[Int],
  v3: Vec[String]
): Vec[(String, Int)] = {
  v3.zip(v1.concat(v2))
}
