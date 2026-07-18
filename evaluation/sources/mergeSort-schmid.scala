// Port of mergeSort-first-class.scala to Georg's syntax, using a
// monomorphic class instead of a generic trait, an (Int, Int) => Boolean
// parameter instead of the Ordering context bound, and ??? stubs instead
// of runtimeChecked. Does not pass the liquid type check, see
// SchmidBenchmarks.scala.
object MergeSort {
  type Pos = {v: Int if v >= 0}

  def safeDiv(x: Pos, y: {v: Pos if v > 1}): {res: Pos if res < x} = ???

  final class SafeSeq(val len: Pos) {
    def apply(i: {v: Pos if v < this.len}): Int = ???
    def splitAt(i: {v: Pos if v < this.len}): (SafeSeq, SafeSeq) = ???
    def ++(that: SafeSeq): {res: SafeSeq if res.len == this.len + that.len} = ???
    def head: Int = ???
    def take(n: Pos): {res: SafeSeq if res.len == n} = ???
    def tail: {res: SafeSeq if res.len == this.len - 1} = ???
  }

  def merge(left: SafeSeq, right: SafeSeq, ord: (Int, Int) => Boolean): {res: SafeSeq if res.len == left.len + right.len} =
    if (left.len > 0 && right.len > 0) {
      if (ord(left.head, right.head)) left.take(1) ++ merge(left.tail, right, ord)
      else right.take(1) ++ merge(left, right.tail, ord)
    }
    else if (left.len == 0) right
    else left

  def mergeSort(list: SafeSeq, ord: (Int, Int) => Boolean): {res: SafeSeq if res.len == list.len} = {
    val len = list.len
    val middle = safeDiv(len, 2)
    if (middle == 0) list
    else {
      val (left, right) = list.splitAt(middle)
      merge(mergeSort(left, ord), mergeSort(right, ord), ord)
    }
  }

  def test(s: {v: SafeSeq if v.len == 8}, ord: (Int, Int) => Boolean): Unit = {
    val sorted: {v: SafeSeq if v.len == 8} = mergeSort(s, ord)
    ()
  }
}
