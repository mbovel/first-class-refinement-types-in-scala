def max(x: Int, y: Int): {v: Int with v >= x && v >= y && (v == x || v == y)} =
  if x > y then x else y
