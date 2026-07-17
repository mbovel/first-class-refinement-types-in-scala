object mergeSortLength {

  def safeDiv(x: Int, y: Int): Int = ???

  final class SafeSeq(val len: Int) {
    def apply(i: Int): Int = ???
    def splitAt(i: Int): (SafeSeq, SafeSeq) = ???
    def ++(that: SafeSeq): SafeSeq = ???
    def head: Int = ???
    def take(n: Int): SafeSeq = ???
    def tail: SafeSeq = ???
  }

  def merge(left: SafeSeq, right: SafeSeq, ord: (Int, Int) => Boolean): SafeSeq =
    if (left.len > 0 && right.len > 0) {
      if (ord(left.head, right.head)) left.take(1) ++ merge(left.tail, right, ord)
      else right.take(1) ++ merge(left, right.tail, ord)
    }
    else if (left.len == 0) right
    else left

  def mergeSort(list: SafeSeq, ord: (Int, Int) => Boolean): SafeSeq = {
    val len = list.len
    val middle = safeDiv(len, 2)
    if (middle == 0) list
    else {
      val (left, right) = list.splitAt(middle)
      merge(mergeSort(left, ord), mergeSort(right, ord), ord)
    }
  }

  def test(s: SafeSeq, ord: (Int, Int) => Boolean): Unit = {
    val sorted: SafeSeq = mergeSort(s, ord)
    ()
  }
}
