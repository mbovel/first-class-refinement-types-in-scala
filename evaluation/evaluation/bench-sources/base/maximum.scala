trait Ordering[T]:
  def compare(x: T, y: T): Int

given Ordering[Int]:
  def compare(x: Int, y: Int): Int =
    if x < y then -1 else if x > y then 1 else 0

def max[T: Ordering as ord, U <: T](x: U, y: U): U =
  if ord.compare(x, y) >= 0 then x else y

def maximum[T: Ordering, U <: T](xs: List[U]): U = xs.reduce(max)

type Even = Int

def test: Even =
  maximum(List(2, 4))
