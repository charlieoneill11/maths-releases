import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.Basic

namespace Chowla

/-- A coefficient of the normalized truncated power at a rational knot. -/
structure SplineTerm where
  knot : ℚ
  degree : ℕ
  coefficient : ℚ
  deriving DecidableEq

abbrev Spline := List SplineTerm

namespace Spline

/-- Evaluate a rational combination of normalized truncated powers. -/
def eval (p : Spline) (x : ℚ) : ℚ :=
  (p.map fun t =>
    t.coefficient * (if t.knot ≤ x then (x - t.knot) ^ t.degree / t.degree.factorial else 0)).sum

/-- Use the normalized basis to apply any number of lower primitives. -/
def primitive (p : Spline) (n : ℕ) : Spline :=
  p.map fun t => { t with degree := t.degree + n }

/-- Convolve two splines using the truncated-power beta identity. -/
def convolution (p q : Spline) : Spline :=
  p.flatMap fun t => q.map fun u =>
    ⟨t.knot + u.knot, t.degree + u.degree + 1, t.coefficient * u.coefficient⟩

/-- Multiply every coefficient by a constant. -/
def scale (p : Spline) (c : ℚ) : Spline :=
  p.map fun t => { t with coefficient := c * t.coefficient }

/-- Ordinary polynomial coefficients in increasing degree order. -/
abbrev Coefficients := List ℚ

namespace Coefficients

/-- Add coefficient lists, treating missing entries as zero. -/
def add : Coefficients → Coefficients → Coefficients
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (p : Coefficients) (c : ℚ) : Coefficients := p.map (c * ·)

/-- Horner translation from a polynomial in x to one in x − c. -/
def translate (p : Coefficients) (c : ℚ) : Coefficients :=
  p.foldr (fun a q => add [a] (add (0 :: q) (scale q c))) []

end Coefficients

/-- Activate an ordinary polynomial at a knot. Expand it about the knot and convert
its monomial coefficients into normalized truncated-power coefficients. -/
def activate (p : Coefficients) (c : ℚ) : Spline :=
  ((p.translate c).zipIdx).map fun (a, j) => ⟨c, j, a * j.factorial⟩

/-- A polynomial supported on the half-open interval `[lo, hi)`. -/
def piece (p : Coefficients) (lo hi : ℚ) : Spline :=
  activate p lo ++ (activate p hi).scale (-1)


/-- Scale the input by a constant. -/
def Coefficients.scaleInput (p : Coefficients) (c : ℚ) : Coefficients :=
  p.zipIdx.map fun (a, j) => a * c ^ j

/-- Consecutive Legendre polynomials, with exact rational coefficients. -/
def legendreCoefficients : ℕ → Coefficients × Coefficients
  | 0 => ([1], [0, 1])
  | n + 1 =>
    let (p, q) := legendreCoefficients n
    let xq := Coefficients.scale (0 :: q) (2 * (n : ℚ) + 3)
    let p' := Coefficients.scale p (-((n : ℚ) + 1))
    (q, (xq.add p').scale (((n : ℚ) + 2)⁻¹))

/-- The rational Legendre profile of Definition 20 in the truncated-power basis. -/
def legendreProfile (s : ℚ) (cs : List ℚ) : Spline :=
  let coeffs : Coefficients := cs.zipIdx.foldr (fun (a, j) p =>
    ((legendreCoefficients (2 * (j + 1))).1.scale a).add p) []
  piece (coeffs.scaleInput s⁻¹) (-s) s

end Spline
end Chowla
