type Pos = Int

case class Matrix(width: Pos, height: Pos):
  def transpose(): Matrix =
    Matrix(height, width)

  def mul(that: Matrix): Matrix =
    Matrix(that.width, height)

def main =
  val m1 = Matrix(2, 3)
  val m2 = Matrix(3, 2)
  m1.mul(m2)

  val m1T = m1.transpose()
  m1T.mul(m1)
