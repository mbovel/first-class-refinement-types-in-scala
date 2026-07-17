object Sqrt:

  def max(x: BigInt, y: BigInt): BigInt =
    if x > y then x else y

  def sqrt(z: BigInt): BigInt =
    z

  def test(u: BigInt): BigInt =
    sqrt(max(0, u))
