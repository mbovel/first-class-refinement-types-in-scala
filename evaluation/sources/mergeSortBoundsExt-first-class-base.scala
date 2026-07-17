

def safeDiv(x: Int, y: Int): Int =
  x / y

object SafeSeqs:
  opaque type SafeSeq[T] = Seq[T]
  object SafeSeq:
    def fromSeq[T](seq: Seq[T]): SafeSeq[T] = seq
    def apply[T](elems: T*): SafeSeq[T] = fromSeq(elems)
  extension [T](a: SafeSeq[T])
    def len: Int = a.length.runtimeChecked
    def apply(i: Int): T =  a(i)
    def splitAt(i: Int): (SafeSeq[T], SafeSeq[T]) = a.splitAt(i)
    def ++(that: SafeSeq[T]): SafeSeq[T] = a ++ that
  extension [T](a: SafeSeq[T])
    def head: T = a.head
    def tail: SafeSeq[T] = a.tail

import SafeSeqs.*

def merge[T: Ordering as ord](left: SafeSeq[T], right: SafeSeq[T]): SafeSeq[T] =
  if left.len > 0 && right.len > 0 then
    if ord.lt(left.head, right.head) then SafeSeq(left.head) ++ merge(left.tail, right)
    else SafeSeq(right.head) ++ merge(left, right.tail)
  else if left.len == 0 then right
  else left

def mergeSort[T: Ordering](list: SafeSeq[T]): SafeSeq[T] =
  val len = list.len
  val middle = safeDiv(len, 2)
  if middle == 0 then list
  else
    val (left, right) = list.splitAt(middle)
    merge(mergeSort(left), mergeSort(right))
