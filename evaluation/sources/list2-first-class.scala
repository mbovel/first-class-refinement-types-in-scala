object Foo {
  type NonNeg = {v: Int with v >= 0}
  val nnList = List[NonNeg](1, 2, 3)
  val nnListRev: List[NonNeg] = nnList.reverse
}
