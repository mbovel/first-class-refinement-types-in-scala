case class DepMap[K, V](p: (K, V) => Boolean):
  def put(n: K, v: V): Unit = ???
  def get(n: K): Option[V] = ???

def fib(n: Int): Int =
  if n <= 1 then 1 else fib(n - 1) + fib(n - 2)

val cache: DepMap[Int, Int] =
  DepMap[Int, Int]((k, v) => v == fib(k))

def fibMemo(n: Int): Int =
  cache.get(n) match
    case Some(res) => res
    case None =>
      val res: Int =
        if n <= 1 then 1 else fibMemo(n - 1) + fibMemo(n - 2)
      cache.put(n, res)
      res
