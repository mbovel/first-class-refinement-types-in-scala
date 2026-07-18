import stainless.lang._

object MergeSort {

  def safeDiv(x: BigInt, y: BigInt): BigInt = {
    (??? : BigInt)
  }

  trait SafeSeq[T] {
    def len: BigInt = {
      (??? : BigInt)
    }

    def apply(i: BigInt): T = {
      (??? : T)
    }

    def splitAt(i: BigInt): (SafeSeq[T], SafeSeq[T]) = {
      (??? : (SafeSeq[T], SafeSeq[T]))
    }

    def ++(that: SafeSeq[T]): SafeSeq[T] = {
      (??? : SafeSeq[T])
    }

    def head: T = {
      (??? : T)
    }

    def take(n: BigInt): SafeSeq[T] = {
      (??? : SafeSeq[T])
    }

    def tail: SafeSeq[T] = {
      (??? : SafeSeq[T])
    }
  }

  def merge[T](left: SafeSeq[T], right: SafeSeq[T], ord: (T, T) => Boolean): SafeSeq[T] = {
    if left.len > 0 && right.len > 0 then
      if ord(left.head, right.head) then left.take(1) ++ merge(left.tail, right, ord)
      else right.take(1) ++ merge(left, right.tail, ord)
    else if left.len == 0 then right
    else left
  }

  def mergeSort[T](list: SafeSeq[T], ord: (T, T) => Boolean): SafeSeq[T] = {
    val len = list.len
    val middle = safeDiv(len, 2)
    if middle == 0 then list
    else
      val (left, right) = list.splitAt(middle)
      merge(mergeSort(left, ord), mergeSort(right, ord), ord)
  }

  def test(s: SafeSeq[Int], ord: (Int, Int) => Boolean): Unit = {
    val sorted = mergeSort(s, ord)
    ()
  }
}
