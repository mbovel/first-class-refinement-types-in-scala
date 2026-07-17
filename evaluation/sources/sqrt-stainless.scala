import stainless.lang._

object Sqrt:

  def max(x: BigInt, y: BigInt): BigInt = {
    if x > y then x else y
  }.ensuring(res => res >= x && res >= y)

  def sqrt(z: BigInt): BigInt = {
    require(z >= 0)
    z
  }

  def test(u: BigInt): BigInt =
    sqrt(max(0, u))
