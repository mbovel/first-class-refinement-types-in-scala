import stainless.lang._
import stainless.annotation._

object MatrixDims:

  case class Matrix(width: BigInt, height: BigInt):
    require(width >= 0 && height >= 0)

    def transpose(): Matrix = {
      Matrix(height, width)
    }.ensuring(res => res.width == height && res.height == width)

    def mul(that: Matrix): Matrix = {
      require(that.height == width)
      Matrix(that.width, height)
    }.ensuring(res => res.width == that.width && res.height == height)

  def main(): Unit = {
    val m1 = Matrix(BigInt(2), BigInt(3))
    val m2 = Matrix(BigInt(3), BigInt(2))
    m1.mul(m2)

    val m1T = m1.transpose()
    m1T.mul(m1)
  }
