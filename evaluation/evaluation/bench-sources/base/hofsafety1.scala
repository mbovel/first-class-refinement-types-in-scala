type NonNeg = Int

def g(f: NonNeg => Int): Int = f(0)

val r = g((x: NonNeg) => x)
