type NonNeg = {v: Int with v >= 0}

def g(f: NonNeg => Int): Int = f(0)

val r = g((x: NonNeg) => x)
