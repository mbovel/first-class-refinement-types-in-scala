object Max {
  def max(x: Int, y: Int): { v: Int if v >= x && v >= y } =
    if (x > y) x else y
}
