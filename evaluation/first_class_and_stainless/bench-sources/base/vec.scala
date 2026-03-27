type Vec[T]

object Vec:
  def fill[T](n: Int, v: T): Vec[T] = ???

extension [T](a: Vec[T])
  def len: Int = ???
  def concat(b: Vec[T]): Vec[T] = ???
  def zip[S](b: Vec[S]): Vec[(T, S)] = ???

@main def Test =
  val n: Int = ???
  val m: Int = ???
  val v1 = Vec.fill(n, 0)
  val v2 = Vec.fill(m, 1)
  val v3 = v1.concat(v2)
  val mPlusN = m + n
  val v4: Vec[(String, Int)] = Vec.fill(mPlusN, "").zip(v3)
