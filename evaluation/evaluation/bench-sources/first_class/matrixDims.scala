type Pos = {v: Int with v >= 0}

case class Matrix(width: Pos, height: Pos):
  def transpose(): {v: Matrix with v.width == height && v.height == width} =
    Matrix(height, width)

  def mul(that: Matrix with that.height == width):
    {v: Matrix with v.width == that.width && v.height == height}
  =
    Matrix(that.width, height)

def main =
  val m1 = Matrix(2, 3)
  val m2 = Matrix(3, 2)
  m1.mul(m2)

  val m1T = m1.transpose()
  m1T.mul(m1)
