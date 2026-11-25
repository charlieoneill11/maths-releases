import HadwigerNelson.Angular.Profile
import HadwigerNelson.Arithmetic.Interpolation

namespace HadwigerNelson.Angular
open Arithmetic Set
private theorem profileEntry (i : Nat) (hi : i < 2049) :
    CompleteWave.profile[i]?.getD 0 = CompleteWave.ordinate i := by
  simp [CompleteWave.profile,hi]

theorem scaled_on_cell (i : Nat) (hi : i < 2048) {z : ℝ}
    (hz : z ∈ Icc (↑(i*CompleteWave.step):ℝ) (↑((i+1)*CompleteWave.step):ℝ)) :
    (CompleteWave.scale:ℝ)*CompleteWave.rightAt (z/CompleteWave.scale) =
      linearAt (↑(i*CompleteWave.step):ℝ) (↑(CompleteWave.profile[i]?.getD 0):ℝ)
        (↑((i+1)*CompleteWave.step):ℝ) (↑(CompleteWave.profile[i+1]?.getD 0):ℝ) z := by
  let S : ℝ := CompleteWave.scale
  let h : ℝ := CompleteWave.step
  have hs : 0<h := by norm_num [h,CompleteWave.step]
  have units : 4096*(z/S) = z/h := by norm_num [S,h,CompleteWave.step,CompleteWave.scale]; ring
  have low : (i:ℝ)*h ≤ z := by simpa [h] using hz.1
  have high : z ≤ ((i:ℝ)+1)*h := by simpa [h] using hz.2
  have cell : 4096*(z/S) ∈ Icc (i:ℝ) ((i:ℝ)+1) := by
    rw [units]
    exact ⟨(le_div_iff₀ hs).2 low,(div_le_iff₀ hs).2 high⟩
  rw [profileEntry i (by omega),profileEntry (i+1) (by omega)]
  unfold CompleteWave.rightAt
  rw [Grid.interpolation_on _ hi cell]
  unfold linearAt
  push_cast
  norm_num [S,h,CompleteWave.step,CompleteWave.scale]
  ring

end HadwigerNelson.Angular
