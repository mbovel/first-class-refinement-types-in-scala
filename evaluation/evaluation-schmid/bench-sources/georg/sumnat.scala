object Foo {
  type NonNeg = { v: Int if v >= 0 }
  type AnyInt = { v: Int if true }

  def safeAdd(x: NonNeg, y: NonNeg): NonNeg =
    if (x + y < 0) 2147483647 else x + y

  def sumNat(n: AnyInt): NonNeg =
    if (n <= 0) {
      0
    } else {
      safeAdd(sumNat(n - 1), n)
    }
}
