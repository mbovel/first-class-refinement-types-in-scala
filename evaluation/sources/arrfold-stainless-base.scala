type NonNeg = Int

class IntArray(val length: NonNeg, init: Int):
  private val data = Array.fill(length)(init)

  def access(i: NonNeg): Int =
    data(i)

def arrFold[A](f: (A, Int) => A, arr: IntArray, z: A): A =
  def rec(i: NonNeg, acc: A): A =
    if i < arr.length then rec(i + 1, f(acc, arr.access(i)))
    else acc
  rec(0, z)

def arrSum(arr: IntArray): Int =
  arrFold[Int](_ + _, arr, 0)

def max(x: Int, y: Int): Int =
  if x > y then x else y

def arrMax(arr: IntArray): NonNeg =
  arrFold[NonNeg](max, arr, 0)
