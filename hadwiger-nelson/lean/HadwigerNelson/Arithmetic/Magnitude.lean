import HadwigerNelson.Arithmetic.Gaussian
import HadwigerNelson.Arithmetic.SquareRoot

/-! From per-arc phase errors to lower bounds for a sum of Fourier contributions. -/

open scoped BigOperators

namespace HadwigerNelson.Arithmetic

/-- Signed contributions accumulate at most the absolute coefficient mass times
the uniform per-arc error. The integrator's mass includes repeated spans. -/
theorem moment_sum_error {ι : Type*} (spans : Finset ι) (c : ι → Int) (f g : ι → ℂ)
    (e : ℝ) (he : ∀ i ∈ spans, ‖f i-g i‖ ≤ e) :
    ‖(∑ i ∈ spans, (c i:ℂ)*f i) - ∑ i ∈ spans, (c i:ℂ)*g i‖ ≤
      (∑ i ∈ spans, |(c i:ℝ)|)*e := by
  rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub,Complex.norm_mul,Complex.norm_intCast]
  exact mul_le_mul_of_nonneg_left (he i hi) (abs_nonneg _)

/-- Round the approximate magnitude down and subtract a proved allowance.
The complex number z is in the same integer units as the stored coordinates. -/
theorem magnitude_sub_allowance (x y k allowance : Int) (z : ℂ) (hk : 0 < k)
    (herr : ‖(⟨(x:ℝ),(y:ℝ)⟩:ℂ)-z‖/(k:ℝ) ≤ allowance) :
    ((Int.sqrt (x*x+y*y)/k-allowance : Int) : ℝ) ≤ ‖z‖/(k:ℝ) := by
  let w : ℂ := ⟨x,y⟩
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hround : ((Int.sqrt (x*x+y*y)/k : Int) : ℝ) ≤ ‖w‖/(k:ℝ) := by
    simpa [w,Complex.norm_def,Complex.normSq_mk,sq] using magnitude_floor x y k hk
  have htri : ‖w‖/(k:ℝ) ≤ ‖w-z‖/k + ‖z‖/k := by
    rw [← add_div]
    exact (div_le_div_iff_of_pos_right hk').2 (norm_le_norm_sub_add _ _)
  change ‖w-z‖/(k:ℝ) ≤ allowance at herr
  push_cast
  linarith only [hround,htri,herr]

end HadwigerNelson.Arithmetic
