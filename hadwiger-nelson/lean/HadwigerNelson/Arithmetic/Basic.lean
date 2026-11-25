import Std

/-! Integer operations shared by the certified executable checkers. -/

namespace HadwigerNelson.Arithmetic

/-- Ceiling division with a signed numerator. Its enclosure lemmas assume a positive divisor. -/
def ceilDiv (a b : Int) : Int := -((-a) / b)

def interpUp (z₀ w₀ z₁ w₁ z : Int) : Int :=
  w₀ + ceilDiv ((w₁-w₀)*(z-z₀)) (z₁-z₀)

def interpDown (z₀ w₀ z₁ w₁ z : Int) : Int :=
  w₀ + ((w₁-w₀)*(z-z₀)) / (z₁-z₀)

/-- Integer upper enclosure. Only the triangle with an interior zero needs rounding. -/
def positiveArea2Up (u v width : Int) : Int :=
  let a := min u v
  let b := max u v
  if b ≤ 0 then 0 else if 0 ≤ a then (a+b)*width else ceilDiv (b*b*width) (b-a)

end HadwigerNelson.Arithmetic
