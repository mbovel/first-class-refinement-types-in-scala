import stainless.lang._

object MaxBench:

  def max(x: BigInt, y: BigInt): BigInt = {
    if x > y then x else y
  }.ensuring(res => res >= x && res >= y && (res == x || res == y))
