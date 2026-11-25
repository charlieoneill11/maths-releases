import HadwigerNelson.Angular.Integral
import HadwigerNelson.Angular.ScaledCell

namespace HadwigerNelson.Angular
open Arithmetic MeasureTheory Set

/-- Real area of an arbitrarily clipped complete-wave slice in physical
coordinates, bounded by the executable tree in doubled integer-area units. -/
theorem slice_scaled_le (d lo : Int) (hlo : 0 ≤ lo) :
    2*(CompleteWave.scale:ℝ)^2 *
      (∫ y in (lo:ℝ)/CompleteWave.scale..(max (CompleteWave.height:Int) lo : Int)/ (CompleteWave.scale:ℝ),
        max 0 (CompleteWave.rightAt y-(d:ℝ)/CompleteWave.scale)) ≤
    ((tabulate CompleteWave.profile CompleteWave.step 11 0).fastArea d lo : ℝ) := by
  let s : ℝ := CompleteWave.scale
  let f := fun z : ℝ => s*CompleteWave.rightAt (z/s)
  have hf : Continuous f := continuous_const.mul
    (CompleteWave.rightAt_continuous.comp (continuous_id.div_const _))
  have h := tabulate_integral_le CompleteWave.profile CompleteWave.step (by decide)
    f hf d lo 11 0 (fun q _ hq z hz => scaled_on_cell q (by omega) hz)
  have sc := integral_scaled_positive CompleteWave.rightAt (lo:ℝ) (max (CompleteWave.height:Int) lo)
    (d:ℝ) s (by norm_num [s,CompleteWave.scale])
  rw [Segments.fastArea_eq _ (tabulate_valid _ _ (by decide) _ _)]
  change _ ≤ ((tabulate CompleteWave.profile CompleteWave.step 11 0).area d lo : ℝ)
  have hp : (0:ℝ) ≤ lo := by exact_mod_cast hlo
  have hh : (CompleteWave.height : ℝ) = ↑((0+2^11)*CompleteWave.step : Nat) := by norm_num [CompleteWave.height, CompleteWave.scale, CompleteWave.step]
  simp only [Int.cast_max,Int.cast_natCast,hh] at sc ⊢
  simp only [Nat.zero_mul,Nat.cast_zero,max_eq_right hp] at h
  change 2*((∫ z in (lo:ℝ).._, max 0 (s*CompleteWave.rightAt (z/s)-d))) ≤ _ at h
  rw [sc] at h
  linarith only [h]

end HadwigerNelson.Angular
