import HadwigerNelson.Arithmetic.Gaussian
import HadwigerNelson.Arithmetic.Rays
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Exact rational coordinates of the phase at a quarter-circle angular bin endpoint. -/

namespace HadwigerNelson.Arithmetic

theorem cos_two_arctan (t : ℝ) : Real.cos (2*Real.arctan t) = rayX t := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  dsimp [rayX]
  have hd : 1+t^2 ≠ 0 := by positivity
  field_simp
  ring

theorem sin_two_arctan (t : ℝ) : Real.sin (2*Real.arctan t) = rayY t := by
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have hd : 0 ≤ 1+t^2 := by positivity
  calc
    _ = (2*t)/(Real.sqrt (1+t^2)*Real.sqrt (1+t^2)) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hd]; rfl

/-- Integers for a counterclockwise rotation by q quarter turns. -/
def quadrant (q : Nat) (x y : Int) : Int × Int :=
  match q%4 with
  | 0 => (x,y)
  | 1 => (-y,x)
  | 2 => (-x,-y)
  | _ => (y,-x)

private theorem quadrant_eq (q : Nat) (x y d : Int) :
    (⟨((quadrant q x y).1:ℝ)/d,((quadrant q x y).2:ℝ)/d⟩:ℂ) =
      Complex.I^q * (⟨(x:ℝ)/d,(y:ℝ)/d⟩:ℂ) := by
  rw [Complex.I_pow_eq_pow_mod]
  have cases : q%4=0 ∨ q%4=1 ∨ q%4=2 ∨ q%4=3 := by omega
  rcases cases with h|h|h|h <;>
    apply Complex.ext <;> simp [quadrant,h,pow_succ,Complex.mul_re,Complex.mul_im,neg_div]

/-- Exact endpoint used by a star run, including the quadrant rotation. -/
theorem phase_integer_point (N j : Int) (q : Nat) (hN : 0 < N) :
    let d := rayDen N j
    let p := quadrant q (N*N-j*j) (2*N*j)
    Complex.exp (((q:ℝ)*Real.pi/2 + 2*Real.arctan ((j:ℝ)/N) : ℝ)*Complex.I) =
      (⟨(p.1:ℝ)/d,(p.2:ℝ)/d⟩:ℂ) := by
  dsimp only
  rw [quadrant_eq]
  let t := (j:ℝ)/N
  have hbase : Complex.exp (↑(2*Real.arctan t)*Complex.I) =
      (⟨((N*N-j*j : Int):ℝ)/(rayDen N j : ℝ),((2*N*j : Int):ℝ)/(rayDen N j : ℝ)⟩:ℂ) := by
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re, cos_two_arctan]
      simpa [t,rayXNum] using scaled_rayX 1 N j hN
    · rw [Complex.exp_ofReal_mul_I_im, sin_two_arctan]
      simpa [t,rayYNum] using scaled_rayY 1 N j hN
  rw [← hbase]
  rw [Complex.ofReal_add,add_mul,Complex.exp_add]
  congr 1
  calc
    _ = Complex.exp ((q:ℂ)*((Real.pi:ℂ)/2*Complex.I)) := by
      congr 1
      push_cast
      ring
    _ = _ := by rw [Complex.exp_nat_mul,Complex.exp_pi_div_two_mul_I]

/-- Error for the harmonic of the actual rational endpoint at every quadrant. -/
theorem star_phase_error (S N j : Int) (q k : Nat) (hS : 0 < S) (hN : 0 < N)
    (hk : (6*k:ℝ) ≤ S) :
    let d := rayDen N j
    let p := quadrant q (N*N-j*j) (2*N*j)
    let theta := (q:ℝ)*Real.pi/2 + 2*Real.arctan ((j:ℝ)/N)
    ‖GaussianInt.value S (GaussianInt.power S (GaussianInt.ofRay S p.1 p.2 d) k) -
      Complex.exp ((k:ℂ)*((theta:ℂ)*Complex.I))‖ ≤ 6*k/(S:ℝ) := by
  dsimp only
  rw [Complex.exp_nat_mul]
  apply GaussianInt.power_error _ _ _ _ hS hk (Complex.norm_exp_ofReal_mul_I _) _
  rw [phase_integer_point N j q hN]
  exact GaussianInt.ofRay_error _ _ _ _ hS (rayDen_pos j hN)

end HadwigerNelson.Arithmetic
