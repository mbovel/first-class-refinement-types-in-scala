import stainless.lang._

object Foo {
  trait Vec[T] {
    def len: BigInt

    def concat(b: Vec[T]): Vec[T] = {
      (??? : Vec[T])
    }.ensuring(r => r.len == this.len + b.len)

    def zip[S](b: Vec[S]): Vec[(T, S)] = {
      require(b.len == this.len)
      (??? : Vec[(T, S)])
    }.ensuring(r => r.len == this.len)
  }

  def example3(
    n: BigInt,
    m: BigInt,
    v1: Vec[Int],
    v2: Vec[Int],
    v3: Vec[String]
  ): Vec[(String, Int)] = {
    require(v1.len == n && v2.len == m && v3.len == n + m)
    v3.zip(v1.concat(v2))
  }.ensuring(r => r.len == m + n)
}
