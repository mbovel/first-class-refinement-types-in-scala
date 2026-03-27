import stainless.lang._

object SumNatBench:

  def safeAdd(x: BigInt, y: BigInt): BigInt = {
    require(x >= 0 && y >= 0)
    x + y
  }.ensuring(res => res >= 0)

  def sumNat(n: BigInt): BigInt = {
    require(n >= 0)
    if n == 0 then BigInt(0)
    else safeAdd(sumNat(n - 1), n)
  }.ensuring(res => res >= 0)
