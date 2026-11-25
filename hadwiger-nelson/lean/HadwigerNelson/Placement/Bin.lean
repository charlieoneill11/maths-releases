import HadwigerNelson.Placement.Overlap
import HadwigerNelson.Placement.TwoTiles

/-! The two outward-rounded displacements in a bin of Proposition 12. -/

open HadwigerNelson.Wave Set

namespace HadwigerNelson.Placement

noncomputable section

def reflectedLow (lo hi : ℝ) : ℝ := max 0 (max (3/4-hi) (lo-3/4))
def reflectedHigh (lo hi : ℝ) : ℝ := max (3/4-lo) (hi-3/4)

theorem left_increasing_upper (W : Datum) : MonotoneOn W.left (Icc (H/2) H) := by
  intro x hx y hy hxy
  have flip (t : ℝ) : W.left (H-t) = W.left t := by rw [W.left_periodic.sub_eq', W.left_even]
  rw [← flip x, ← flip y]
  apply W.left_antitone <;> first | constructor <;> linarith [hx.1,hx.2,hy.1,hy.2] | linarith

theorem reflected_enclosure {lo hi v : ℝ} (hl : lo ≤ v) (hh : v ≤ hi) :
    reflectedLow lo hi ≤ |3/4-v| ∧ |3/4-v| ≤ reflectedHigh lo hi := by
  constructor
  · refine max_le (abs_nonneg _) (max_le ?_ ?_)
    · exact le_trans (by linarith) (le_abs_self (3/4-v))
    · exact le_trans (by linarith) (neg_le_abs (3/4-v))
  · rw [abs_le, reflectedHigh]
    exact ⟨by linarith [le_max_right (3/4-lo) (hi-3/4)],by linarith [le_max_left (3/4-lo) (hi-3/4)]⟩

/-- The real inequality that an arithmetic box has to instantiate. In particular both `lo ≥ H`
cases are evaluated according to the definition of `sliceUpper`. -/
theorem monoProb_box (W : Datum) {u v xmin xmax ymin ymax : ℝ}
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) (hx : u ∈ Icc xmin xmax) (hy : v ∈ Icc ymin ymax)
    (hymin : 0 ≤ ymin) :
    W.x * H * directionalMonoProb W (point u v) ≤
      sliceUpper W.left W.right H xmin ymin ymax +
        sliceUpper W.left W.right H (2*W.x-xmax) (reflectedLow ymin ymax) (reflectedHigh ymin ymax) := by
  have hpos : 0 < W.x * H := mul_pos (by linarith [W.x_bounds.1]) H_pos
  have h := (le_div_iff₀ hpos).mp (monoProb_eq_covariograms W hu hv).le
  rw [mul_comm] at h
  refine h.trans (add_le_add ?_ ?_)
  · rw [tileCovariogram_eq_sliceArea W.left_continuous W.right_continuous hv.1]
    exact sliceArea_le_sliceUpper W.left_continuous W.right_continuous W.left_antitone (left_increasing_upper W)
      hymin hy.1 hy.2 hx.1
  · rw [tileCovariogram_eq_sliceArea W.left_continuous W.right_continuous (abs_nonneg _)]
    have hab := reflected_enclosure hy.1 hy.2
    exact sliceArea_le_sliceUpper W.left_continuous W.right_continuous W.left_antitone (left_increasing_upper W)
      (le_max_left _ _) hab.1 hab.2 (by linarith [hx.2])

end
end HadwigerNelson.Placement
