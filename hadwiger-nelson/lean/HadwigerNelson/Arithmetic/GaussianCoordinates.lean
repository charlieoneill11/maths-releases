import HadwigerNelson.Arithmetic.GaussianInt
import HadwigerNelson.Arithmetic.Rounding
import Mathlib.Data.Complex.Basic

namespace HadwigerNelson.Arithmetic.GaussianInt

noncomputable def value (S : Int) (a : GaussianInt) : ℂ := ⟨a.re/S, a.im/S⟩

private theorem component_error (a S : Int) (hS : 0 < S) :
    |((a.tdiv S : Int):ℝ)/S - (a:ℝ)/S/S| ≤ 1/(S:ℝ) := by
  have hSr : (0:ℝ) < S := by exact_mod_cast hS
  rw [← sub_div,abs_div,abs_of_pos hSr]
  exact (div_le_div_iff_of_pos_right hSr).2 (tdiv_error _ hS).le

/-- Each real coordinate of a truncated product has an error of at most one tick. -/
theorem mul_coordinate_error (S : Int) (a b : GaussianInt) (hS : 0 < S) :
    let d := value S (mul S a b) - value S a * value S b
    |d.re| ≤ 1/(S:ℝ) ∧ |d.im| ≤ 1/(S:ℝ) := by
  let d := value S (mul S a b) - value S a * value S b
  have hre : |d.re| ≤ 1 / (S:ℝ) := by
    have h := component_error (a.re*b.re-a.im*b.im) S hS
    dsimp [d,value,mul,Complex.sub_re,Complex.mul_re]
    push_cast at h
    convert h using 2
    ring
  have him : |d.im| ≤ 1 / (S:ℝ) := by
    have h := component_error (a.re*b.im+a.im*b.re) S hS
    dsimp [d,value,mul,Complex.sub_im,Complex.mul_im]
    push_cast at h
    convert h using 2
    ring
  exact ⟨hre,him⟩

private theorem floor_scaled_error (S a den : Int) (hS : 0 < S) (hd : 0 < den) :
    |(((S*a)/den : Int):ℝ)/S - (a:ℝ)/den| < 1/(S:ℝ) := by
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have hlo := floorDiv_le_real (S*a) hd
  have hhi := real_lt_floorDiv_add_one (S*a) hd
  push_cast at hlo hhi
  rw [show (S:ℝ)*a/den = (a:ℝ)/den*S by ring] at hlo hhi
  rw [abs_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ hS').2 hlo)),neg_sub,
    lt_div_iff₀ hS']
  rw [sub_mul,div_mul_cancel₀ _ hS'.ne']
  linarith

theorem ofRay_coordinate_error (S x y den : Int) (hS : 0 < S) (hd : 0 < den) :
    let z := value S (ofRay S x y den)
    |z.re - (x:ℝ)/den| < 1/(S:ℝ) ∧ |z.im - (y:ℝ)/den| < 1/(S:ℝ) :=
  ⟨floor_scaled_error S x den hS hd,floor_scaled_error S y den hS hd⟩

end HadwigerNelson.Arithmetic.GaussianInt
