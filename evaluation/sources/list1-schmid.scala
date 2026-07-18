object Foo {
  type NonNeg = {v: Int if v >= 0}
  val nnList = List[NonNeg](1, 2, 3)
  val nnInt: NonNeg = nnList.head
}
