object MergeSortBounds {
  class SafeSeq[T](private val data: Seq[T]) {
    def len: Int = data.length
    def apply(i: Int): T = data(i)
    def splitAt(i: Int): (SafeSeq[T], SafeSeq[T]) = {
      val (l, r) = data.splitAt(i)
      (new SafeSeq(l), new SafeSeq(r))
    }
    def ++(that: SafeSeq[T]): SafeSeq[T] = new SafeSeq(data ++ that.data)
  }

  def head[T](s: SafeSeq[T]): T = s(0)
  def tail[T](s: SafeSeq[T]): SafeSeq[T] = s.splitAt(1)._2

  def safeDiv(x: Int, y: Int): Int =
    x / y

  def merge[T](left: SafeSeq[T], right: SafeSeq[T], ord: (T, T) => Boolean): SafeSeq[T] =
    if (left.len > 0 && right.len > 0)
      if (ord(head(left), head(right))) new SafeSeq(Seq(head(left))) ++ merge(tail(left), right, ord)
      else new SafeSeq(Seq(head(right))) ++ merge(left, tail(right), ord)
    else if (left.len == 0) right
    else left

  def mergeSort[T](list: SafeSeq[T], ord: (T, T) => Boolean): SafeSeq[T] = {
    val len = list.len
    val middle = safeDiv(len, 2)
    if (middle == 0) list
    else {
      val (left, right) = list.splitAt(middle)
      merge(mergeSort(left, ord), mergeSort(right, ord), ord)
    }
  }
}
