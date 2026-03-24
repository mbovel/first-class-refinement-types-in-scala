import stainless.lang._
import stainless.annotation._

object RangeBench:

  sealed abstract class MyList[T]
  case class MyCons[T](head: T, tail: MyList[T]) extends MyList[T]
  case class MyNil[T]() extends MyList[T]

  @extern
  def myApply[T](l: MyList[T], i: BigInt): T = ???

  case class CheckedArray(size: BigInt, data: MyList[BigInt]):
    require(size >= 0)

  def get(a: CheckedArray, i: BigInt): BigInt = {
    require(i >= 0 && i < a.size)
    myApply(a.data, i)
  }

  def testLoop(a: CheckedArray, from: BigInt): Unit = {
    require(from >= 0 && from <= a.size)
    decreases(a.size - from)
    if from < a.size then
      get(a, from)
      testLoop(a, from + 1)
  }

  def test(l: MyList[BigInt]): Unit = {
    val a = CheckedArray(BigInt(10), l)
    testLoop(a, BigInt(0))
  }
