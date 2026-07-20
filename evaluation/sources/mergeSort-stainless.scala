import stainless.lang._

object MergeSort {

  def safeDiv(x: Int, y: Int): Int = {
    require(x >= 0 && y > 1)
    (??? : Int)
  }.ensuring(res => res >= 0 && res < x)

  trait SafeSeq[T] {
    def len: Int = {
      (??? : Int)
    }.ensuring(res => res >= 0)

    def apply(i: Int): T = {
      require(0 <= i && i < this.len)
      (??? : T)
    }

    def splitAt(i: Int): (SafeSeq[T], SafeSeq[T]) = {
      require(0 <= i && i < this.len)
      (??? : (SafeSeq[T], SafeSeq[T]))
    }.ensuring(p => p._1.len + p._2.len == this.len)

    def ++(that: SafeSeq[T]): SafeSeq[T] = {
      (??? : SafeSeq[T])
    }.ensuring(res => res.len == this.len + that.len)

    def head: T = {
      (??? : T)
    }

    def take(n: Int): SafeSeq[T] = {
      require(n >= 0)
      (??? : SafeSeq[T])
    }.ensuring(res => res.len == n)

    def tail: SafeSeq[T] = {
      (??? : SafeSeq[T])
    }.ensuring(res => res.len == this.len - 1)
  }

  def merge[T](left: SafeSeq[T], right: SafeSeq[T], ord: (T, T) => Boolean): SafeSeq[T] = {
    if left.len > 0 && right.len > 0 then
      if ord(left.head, right.head) then left.take(1) ++ merge(left.tail, right, ord)
      else right.take(1) ++ merge(left, right.tail, ord)
    else if left.len == 0 then right
    else left
  }.ensuring(res => res.len == left.len + right.len)

  def mergeSort[T](list: SafeSeq[T], ord: (T, T) => Boolean): SafeSeq[T] = {
    val len = list.len
    val middle = safeDiv(len, 2)
    if middle == 0 then list
    else
      val (left, right) = list.splitAt(middle)
      merge(mergeSort(left, ord), mergeSort(right, ord), ord)
  }.ensuring(res => res.len == list.len)

  def test(s: SafeSeq[Int], ord: (Int, Int) => Boolean): Unit = {
    require(s.len == 8)
    val sorted = mergeSort(s, ord)
    assert(sorted.len == 8)
  }
}
