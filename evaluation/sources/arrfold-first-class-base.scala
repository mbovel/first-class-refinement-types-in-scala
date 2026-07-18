object Foo {

  class IntArray(val length: Int, init: Int) {
    private val data = Array.fill(length)(init)

    def access(i: Int): Int =
      data(i)
  }

  def arrFold[A](f: (A, Int) => A, arr: IntArray, z: A): A = {
    def rec(i: Int, acc: A): A =
      if (i < arr.length) rec(i + 1, f(acc, arr.access(i)))
      else acc
    rec(0, z)
  }

  def arrSum(arr: IntArray): Int =
    arrFold[Int](_ + _, arr, 0)

  def max(x: Int, y: Int): Int =
    if (x > y) x else y

  def arrMax(arr: IntArray): Int =
    arrFold[Int](max, arr, 0)
}
