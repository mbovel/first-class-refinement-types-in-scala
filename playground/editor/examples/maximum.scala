def max(x: Int, y: Int): { v: Int with v >= x && v >= y } =
  if (x > y) x else y

// Try swapping the branches above, then compile again.
val m: { v: Int with v >= 3 } = max(3, 7)
