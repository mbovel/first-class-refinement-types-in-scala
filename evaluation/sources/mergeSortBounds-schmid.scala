object MergeSortBounds {
  type NonNeg = { v: Int if v >= 0 }

  final class SafeSeq(val len: NonNeg, val data: Seq[Int]) {
    def apply(i: {v: Int if 0 <= v && v < this.len}): Int = ???
    def update(i: {v: Int if 0 <= v && v < this.len}, x: Int): Unit = ???
    def splitAt(i: {v: Int if 0 <= v && v < this.len}): (SafeSeq, SafeSeq) = ???
    def ++(that: SafeSeq): SafeSeq = ???
  }

  def head(s: { v: SafeSeq if v.len > 0 }): Int = ???
  def tail(s: { v: SafeSeq if v.len > 0 }): SafeSeq = ???

  def merge(left: SafeSeq, right: SafeSeq, ord: (Int, Int) => Boolean): SafeSeq = {
    val leftLen = left.len
    val rightLen = right.len
    if (leftLen > 0 && rightLen > 0) {
      val lh = head(left)
      val lt = tail(left)
      val rh = head(right)
      val rt = tail(right)
      if (ord(lh, rh)) new SafeSeq(1, Seq(lh)) ++ merge(lt, right, ord)
      else new SafeSeq(1, Seq(rh)) ++ merge(left, rt, ord)
    }
    else if (left.len == 0) right
    else left
  }

}
