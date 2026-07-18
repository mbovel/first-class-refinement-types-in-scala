object MergeSort {


  def safeDiv(x: Int, y: Int): Int =
    x / y

  trait SafeSeq[T]:
    def len: Int
    def apply(i: Int): T
    def splitAt(i: Int): (SafeSeq[T], SafeSeq[T])
    def ++(that: SafeSeq[T]): SafeSeq[T]
    def head: T
    def take(n: Int): SafeSeq[T]
    def tail: SafeSeq[T]

  def merge[T: Ordering as ord](left: SafeSeq[T], right: SafeSeq[T]): SafeSeq[T] =
    if left.len > 0 && right.len > 0 then
      if ord.lt(left.head, right.head) then left.take(1) ++ merge(left.tail, right)
      else right.take(1) ++ merge(left, right.tail)
    else if left.len == 0 then right
    else left

  def mergeSort[T: Ordering](list: SafeSeq[T]): SafeSeq[T] =
    val len = list.len
    val middle = safeDiv(len, 2)
    if middle == 0 then list
    else
      val (left, right) = list.splitAt(middle)
      merge(mergeSort(left), mergeSort(right))

  def test(s: SafeSeq[Int]) =
    mergeSort(s): SafeSeq[Int]
    ()
}
