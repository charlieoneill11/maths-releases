import HadwigerNelson.Angular.Scaled
import HadwigerNelson.Angular.Datum
import HadwigerNelson.Placement.Slice

namespace HadwigerNelson.Angular
open Wave Placement MeasureTheory Set

noncomputable section

private abbrev S : ℝ := CompleteWave.scale
private abbrev tree := tabulate CompleteWave.profile CompleteWave.step 11 0
private theorem Spos : (0:ℝ)<S := by norm_num [S,CompleteWave.scale]

theorem scaled_nonneg (d lo : Int) (positive : 0 ≤ lo) : 0 ≤ (tree.fastArea d lo : ℝ) := by
  have h := slice_scaled_le d lo positive
  have up : (lo:ℝ)/S ≤ ((max (CompleteWave.height:Int) lo:Int):ℝ)/S :=
    div_le_div_of_nonneg_right (by exact_mod_cast le_max_right (CompleteWave.height:Int) lo) Spos.le
  have hI := intervalIntegral.integral_nonneg (μ := volume) up (fun t _ => le_max_left 0 (CompleteWave.rightAt t-(d:ℝ)/S))
  exact le_trans (mul_nonneg (by positivity) hI) h

theorem physical_slice (d lo : Int) (hi : ℝ) (positive : 0 ≤ lo) :
    sliceUpper completeDatum.left completeDatum.right H ((d:ℝ)/S) ((lo:ℝ)/S) hi ≤
    (tree.fastArea d lo:ℝ)/(2*S^2) := by
  have left : completeDatum.left = fun _ => 0 := funext completeDatum_left
  rw [left,sliceUpper_zero_left]
  split_ifs with far
  · exact div_nonneg (scaled_nonneg _ _ positive) (by positivity)
  · have exactH : ((CompleteWave.height:Int):ℝ)/S = H := by norm_num [H,S,CompleteWave.height,CompleteWave.scale]
    have close : lo ≤ (CompleteWave.height:Int) := by
      have hlt : (lo:ℝ)/S < ((CompleteWave.height:Int):ℝ)/S := by rw [exactH]; exact lt_of_not_ge far
      have := (div_lt_div_iff_of_pos_right Spos).1 hlt
      exact_mod_cast this.le
    have loPos : 0 ≤ (lo:ℝ)/S := div_nonneg (by exact_mod_cast positive) Spos.le
    have eq : (∫ y in (lo:ℝ)/S..H, max 0 (completeDatum.right y-(d:ℝ)/S)) =
        (∫ y in (lo:ℝ)/S..H, max 0 (CompleteWave.rightAt y-(d:ℝ)/S)) := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le (le_of_not_ge far)] at hz
      simp only [completeDatum_right ⟨loPos.trans hz.1,hz.2⟩]
    rw [eq]
    have h := slice_scaled_le d lo positive
    rw [max_eq_left close,exactH] at h
    apply (le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos Spos))).2
    simpa only [mul_comm _ (2*S^2)] using h

end
end HadwigerNelson.Angular
