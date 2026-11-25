import HadwigerNelson.Arithmetic.GaussianCoordinates
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp

/-! Error bounds for repeated fixed-point complex multiplication in both stars. -/

namespace HadwigerNelson.Arithmetic.GaussianInt

/-- One truncated product is within two reciprocal scale units in complex norm. -/
theorem mul_error (S : Int) (a b : GaussianInt) (hS : 0 < S) :
    ‖value S (mul S a b) - value S a * value S b‖ ≤ 2/(S:ℝ) := by
  obtain ⟨hre,him⟩ := mul_coordinate_error S a b hS
  calc
    _ ≤ _ := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1/(S:ℝ) + 1/S := add_le_add hre him
    _ = _ := by ring

/-- Floor rounding of a rational point on any quadrant of the circle. -/
theorem ofRay_error (S x y den : Int) (hS : 0 < S) (hd : 0 < den) :
    ‖value S (ofRay S x y den) - (⟨(x:ℝ)/den,(y:ℝ)/den⟩:ℂ)‖ ≤ 2/(S:ℝ) := by
  obtain ⟨hr,hi⟩ := ofRay_coordinate_error S x y den hS hd
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp only [Complex.sub_re,Complex.sub_im]
  exact (add_le_add hr.le hi.le).trans_eq (by ring)

/-- Inductive error bound in §3.2. The scale condition holds for every harmonic tested. -/
theorem power_error (S : Int) (base : GaussianInt) (z : ℂ) (k : Nat)
    (hS : 0 < S) (hk : (6*k : ℝ) ≤ S) (hz : ‖z‖ = 1)
    (hbase : ‖value S base - z‖ ≤ 2/(S:ℝ)) :
    ‖value S (power S base k) - z^k‖ ≤ 6*k/(S:ℝ) := by
  have hSr : (0:ℝ) < S := by exact_mod_cast hS
  induction k with
  | zero =>
    have h0 : value S (power S base 0) = 1 := by apply Complex.ext <;> simp [value,power,hSr.ne']
    simp [h0]
  | succ k ih =>
    have hks : 6*(k:ℝ) ≤ S := by exact le_trans (by push_cast; linarith) hk
    have he := ih hks
    have hb : ‖value S base‖ ≤ 1+2/(S:ℝ) := by
      calc
        _ ≤ ‖value S base - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
        _ ≤ _ := by rw [hz]; linarith
    let w := value S (power S base k)
    let b := value S base
    let e := value S (mul S (power S base k) base) - w*b
    have herr : ‖e‖ ≤ 2/(S:ℝ) := mul_error _ _ _ hS
    have hsum : value S (power S base (k+1)) - z^(k+1) =
        e + ((w-z^k)*b+z^k*(b-z)) := by
      dsimp [e,w,b,power]
      ring
    have hsmall : (6*(k:ℝ)/S)*(2/S) ≤ 2/(S:ℝ) := by
      have := (div_le_one hSr).2 hks
      simpa using mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ 2/(S:ℝ))
    rw [hsum]
    calc
      _ ≤ ‖e‖ + (‖(w-z^k)*b‖ + ‖z^k*(b-z)‖) :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ (2/(S:ℝ)) + ((6*k/S)*(1+2/S) + 1*(2/S)) := by
        rw [Complex.norm_mul,Complex.norm_mul,Complex.norm_pow,hz,one_pow]
        exact add_le_add herr (add_le_add
          (mul_le_mul he hb (norm_nonneg _) (by positivity)) (by simpa using hbase))
      _ = 4/S + 6*k/S + ((6*k/S)*(2/S) : ℝ) := by ring
      _ ≤ 4/S + 6*k/S + (2/S : ℝ) := add_le_add_right hsmall _
      _ = _ := by push_cast; ring

/-- A Pythagorean triple supplies a unit complex number with rational coordinates. -/
theorem rational_norm_one (x y den : Int) (hd : 0 < den) (hxy : x*x+y*y = den*den) :
    ‖(⟨(x:ℝ)/den,(y:ℝ)/den⟩:ℂ)‖ = 1 := by
  rw [Complex.norm_def,Complex.normSq_mk]
  have hd' : (0:ℝ) < den := by exact_mod_cast hd
  have hxy' : (x:ℝ)*x+y*y = (den:ℝ)*den := by exact_mod_cast hxy
  have h : (x:ℝ)/den*(x/den)+(y:ℝ)/den*(y/den) = 1 := by
    field_simp
    nlinarith only [hxy']
  rw [h,Real.sqrt_one]

/-- Direct endpoint enclosure for the integer row used by the star checker. -/
theorem rational_power_error (S x y den : Int) (k : Nat) (hS : 0 < S) (hd : 0 < den)
    (hxy : x*x+y*y = den*den) (hk : (6*k:ℝ) ≤ S) :
    ‖value S (power S (ofRay S x y den) k) - (⟨(x:ℝ)/den,(y:ℝ)/den⟩:ℂ)^k‖ ≤ 6*k/(S:ℝ) :=
  power_error _ _ _ _ hS hk (rational_norm_one _ _ _ hd hxy) (ofRay_error _ _ _ _ hS hd)

/-- After division by the harmonic, the difference between two approximate phases
has an error of at most twelve ticks per arc. -/
theorem arc_error (S : Int) (k : Nat) (hk : 0 < k) (w v z y : ℂ)
    (hw : ‖w-z‖ ≤ 6*(k:ℝ)/S) (hv : ‖v-y‖ ≤ 6*(k:ℝ)/S) :
    ‖(w-v)-(z-y)‖/(k:ℝ) ≤ 12/(S:ℝ) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  apply (div_le_iff₀ hk').2
  rw [show (w-v)-(z-y) = (w-z)-(v-y) by ring]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ 6*(k:ℝ)/S + 6*k/S := add_le_add hw hv
    _ = _ := by ring

end HadwigerNelson.Arithmetic.GaussianInt
