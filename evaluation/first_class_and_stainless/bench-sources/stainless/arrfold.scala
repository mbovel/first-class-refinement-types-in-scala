import stainless.collection._
import stainless.lang._

object ArrFoldBench:

  case class IntArray(length: BigInt, data: List[BigInt]):
    require(length >= 0)

    def access(i: BigInt): BigInt = {
      require(i >= 0 && i < length)
      data(i)
    }

  def arrFold(f: (BigInt, BigInt) => BigInt, arr: IntArray, z: BigInt, i: BigInt): BigInt = {
    require(i >= 0 && i <= arr.length)
    if i < arr.length then arrFold(f, arr, f(z, arr.access(i)), i + 1)
    else z
  }

  def arrSum(arr: IntArray): BigInt =
    arrFold(_ + _, arr, BigInt(0), BigInt(0))

  def max(x: BigInt, y: BigInt): BigInt = {
    if x > y then x else y
  }.ensuring(res => res >= x && res >= y)

  def arrMax(arr: IntArray): BigInt =
    arrFold(max, arr, BigInt(0), BigInt(0))
