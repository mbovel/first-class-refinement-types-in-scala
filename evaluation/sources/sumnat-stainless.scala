import stainless.lang._
import stainless.math.wrapping

object Test {

  def safeAdd(x: Int, y: Int): Int = {
    require(x >= 0 && y >= 0)
    if wrapping(x + y) < 0 then 2147483647 else wrapping(x + y)
  }.ensuring(v => v >= 0)

  def sumNat(n: Int): Int = {
    if n <= 0 then
      0
    else
      safeAdd(sumNat(n - 1), n)
  }.ensuring(v => v >= 0)
}
