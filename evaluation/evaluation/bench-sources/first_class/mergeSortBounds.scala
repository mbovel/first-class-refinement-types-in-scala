type Pos = {x: Int with x >= 0}

def safeDiv(x: Pos, y: Pos with y > 1): {res: Pos with res < x} =
  (x / y).runtimeChecked

class SafeSeq[T](val data: Seq[T]):
  def len: Pos = data.length.runtimeChecked
  def apply(i: Pos with i < len): T = data(i)
  def splitAt(i: Pos with i < len): (SafeSeq[T], SafeSeq[T]) = data.splitAt(i)
  def ++(that: SafeSeq[T]): SafeSeq[T] = SafeSeq(data ++ that.data)

def head[T](s: SafeSeq[T] with s.len > 0): T = s.head
def tail[T](s: SafeSeq[T] with s.len > 0): SafeSeq[T] = s.tail

def merge[T: Ordering as ord](left: SafeSeq[T], right: SafeSeq[T]): SafeSeq[T] =
  if left.len > 0 && right.len > 0 then
    if ord.lt(head(left), head(right)) then SafeSeq(Seq(head(left))) ++ merge(tail(left), right)
    else SafeSeq(Seq(head(right))) ++ merge(left, tail(right))
  else if left.len == 0 then right
  else left

def mergeSort[T: Ordering](list: SafeSeq[T]): SafeSeq[T] =
  val len = list.len
  val middle = safeDiv(len, 2)
  if middle == 0 then list
  else
    val (left, right) = list.splitAt(middle)
    merge(mergeSort(left), mergeSort(right))
