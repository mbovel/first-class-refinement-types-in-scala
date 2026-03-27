object Foo {
  def safeAdd(x: Int, y: Int): Int =
    if (x + y < 0) 2147483647 else x + y

  def sumNat(n: Int): Int =
    if (n <= 0) {
      0
    } else {
      safeAdd(sumNat(n - 1), n)
    }
}
