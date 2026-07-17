import stainless.lang._
import stainless.annotation._

object MergeSortBounds:

  sealed abstract class MyList[T]
  case class MyCons[T](head: T, tail: MyList[T]) extends MyList[T]
  case class MyNil[T]() extends MyList[T]

  @extern
  def mySize[T](l: MyList[T]): BigInt = {
    BigInt(0)
  }.ensuring(res => res >= 0)

  @extern
  def myApply[T](l: MyList[T], i: BigInt): T = {
    require(i >= 0 && i < mySize(l))
    ???
  }

  @extern
  def mySplitAtIndex[T](l: MyList[T], i: BigInt): (MyList[T], MyList[T]) = {
    require(i >= 0 && i < mySize(l))
    (l, l)
  }.ensuring(res => mySize(res._1) + mySize(res._2) == mySize(l))

  @extern
  def myConcat[T](l: MyList[T], r: MyList[T]): MyList[T] = {
    l
  }.ensuring(res => mySize(res) == mySize(l) + mySize(r))

  @extern
  def myHead[T](l: MyList[T]): T = {
    require(mySize(l) > 0)
    ???
  }

  @extern
  def myTail[T](l: MyList[T]): MyList[T] = {
    require(mySize(l) > 0)
    l
  }.ensuring(res => mySize(res) == mySize(l) - 1)

  @extern
  def mySingleton[T](x: T): MyList[T] = {
    val r: MyList[T] = MyCons(x, MyNil[T]())
    r
  }.ensuring(res => mySize(res) == BigInt(1))

  case class SafeSeq[T](data: MyList[T]):
    def len: BigInt = {
      mySize(data)
    }.ensuring(res => res >= 0)

    def apply(i: BigInt): T = {
      require(i >= 0 && i < len)
      myApply(data, i)
    }

    def splitAt(i: BigInt): (SafeSeq[T], SafeSeq[T]) = {
      require(i >= 0 && i < len)
      val (l, r) = mySplitAtIndex(data, i)
      (SafeSeq(l), SafeSeq(r))
    }.ensuring(res => res._1.len + res._2.len == len)

    def ++(that: SafeSeq[T]): SafeSeq[T] = {
      SafeSeq(myConcat(data, that.data))
    }.ensuring(res => res.len == len + that.len)

  def head[T](s: SafeSeq[T]): T = {
    require(s.len > 0)
    myHead(s.data)
  }

  def tail[T](s: SafeSeq[T]): SafeSeq[T] = {
    require(s.len > 0)
    SafeSeq(myTail(s.data))
  }.ensuring(res => res.len == s.len - 1)

  def safeDiv(x: BigInt, y: BigInt): BigInt = {
    require(x > 1 && y > 1)
    x / y
  }.ensuring(res => res >= 0)

  def merge[T](left: SafeSeq[T], right: SafeSeq[T])(implicit ord: (T, T) => Boolean): SafeSeq[T] = {
    decreases(left.len + right.len)
    if left.len > 0 && right.len > 0 then
      if ord(head(left), head(right)) then SafeSeq(mySingleton(head(left))) ++ merge(tail(left), right)
      else SafeSeq(mySingleton(head(right))) ++ merge(left, tail(right))
    else if left.len == BigInt(0) then right
    else left
  }

  def mergeSort[T](list: SafeSeq[T])(implicit ord: (T, T) => Boolean): SafeSeq[T] = {
    decreases(list.len)
    val len = list.len
    if len <= 1 then list
    else
      val middle = safeDiv(len, BigInt(2))
      val (left, right) = list.splitAt(middle)
      merge(mergeSort(left), mergeSort(right))
  }
