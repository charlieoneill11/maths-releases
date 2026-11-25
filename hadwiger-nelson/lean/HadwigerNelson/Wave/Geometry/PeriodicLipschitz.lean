import HadwigerNelson.Wave.Geometry
import Mathlib.Data.Real.Archimedean

namespace HadwigerNelson.Wave

/-- A periodic profile which is 1-Lipschitz on one closed period remains
1-Lipschitz when the segment between its arguments crosses a tile seam. -/
theorem periodic_lipschitz {f : ℝ → ℝ} (per : Function.Periodic f H)
    (onCell : ∀ a ∈ Set.Icc 0 H, ∀ b ∈ Set.Icc 0 H, |f a-f b| ≤ |a-b|) (a b : ℝ) :
    |f a-f b| ≤ |a-b| := by
  wlog h : a ≤ b generalizing a b
  · simpa only [abs_sub_comm (f b) (f a),abs_sub_comm b a] using this b a (le_of_not_ge h)
  let i := ⌊a/H⌋
  let j := ⌊b/H⌋
  let u := a-i*H
  let v := b-j*H
  have frac (t : ℝ) : t-⌊t/H⌋*H∈Set.Icc 0 H := by
    have lo := (le_div_iff₀ H_pos).mp (Int.floor_le (t/H))
    have up := (div_lt_iff₀ H_pos).mp (Int.lt_floor_add_one (t/H))
    constructor <;> linarith
  have hu : u∈Set.Icc 0 H := frac a
  have hv : v∈Set.Icc 0 H := frac b
  have ru : f u=f a := per.sub_int_mul_eq i
  have rv : f v=f b := per.sub_int_mul_eq j
  rw [← ru,← rv]
  by_cases eq : i=j
  · have diff : u-v=a-b := by dsimp [u,v]; rw [eq]; ring
    simpa only [diff] using onCell u hu v hv
  have le : i ≤ j := Int.floor_mono (div_le_div_of_nonneg_right h H_pos.le)
  have inc : (i:ℝ)+1 ≤ j := by exact_mod_cast (show i+1≤j by omega)
  have room := mul_le_mul_of_nonneg_right inc H_pos.le
  have near := onCell u hu H ⟨H_pos.le,le_rfl⟩
  have far := onCell 0 ⟨le_rfl,H_pos.le⟩ v hv
  have same : f H=f 0 := by simpa using per 0
  rw [same,abs_of_nonpos (sub_nonpos.mpr hu.2)] at near
  rw [zero_sub,abs_neg,abs_of_nonneg hv.1] at far
  have tri := abs_sub_le (f u) (f 0) (f v)
  rw [abs_of_nonpos (sub_nonpos.mpr h)]
  dsimp [u,v] at near far ⊢
  linarith

end HadwigerNelson.Wave
