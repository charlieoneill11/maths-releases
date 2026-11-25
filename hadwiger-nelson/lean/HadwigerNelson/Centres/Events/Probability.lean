import HadwigerNelson.Centres.Events.SectorBounds
import HadwigerNelson.Centres.Events.ArcProfile
import HadwigerNelson.Native.Centres.Small
import HadwigerNelson.Native.Centres.MediumCoarse
import HadwigerNelson.Native.Centres.MediumFine

namespace HadwigerNelson.Centres.Events
open MeasureTheory Set Placement Quadrature

private theorem nonnegative_cost (p : Profile) : 0≤angleCost p := by
  cases p <;> norm_num [angleCost] <;> split <;> norm_num

private theorem outside (p : Profile) {z l : ℝ} (large : 245/1000≤z) :
    (if δ≤l then (intercept p-angleCost p*(z-δ))/2
      else (smallIntercept p-angleCost p*(z-δR))/2) ≤ 0 := by
  cases p <;> split <;> simp only [intercept,smallIntercept,angleCost] <;>
    split_ifs <;> norm_num [δ,δR] at * <;> linarith

/-- Lemma 49 for the actual product law of rotation and translation. -/
theorem probability_lower (W : Wave.Datum) (hW : partialProfile W) (X D : Finset Plane)
    (p : Profile) (u v : Plane) (ho : orientation X D v u) (hℓ : δR≤chord u v) :
    let l := chord u v
    let z := arcLength X u v
    (if δ≤l then (intercept p-angleCost p*(z-δ))/2
      else (smallIntercept p-angleCost p*(z-δR))/2) ≤
      (law W).real {ω | ω.2∈centreEvent W X D p ω.1 v u} := by
  dsimp only
  have chordArc := chord_le_arcLength X u v
  by_cases range : chord u v ≤ 245/1000
  · by_cases minor : minorArc X u v
    · obtain ⟨φ,phase⟩ := exists_aligned_phase u v
      have hl : chord u v ∈ Icc δR (245/1000) := ⟨hℓ,range⟩
      by_cases smallChord : chord u v ≤ 2/100
      · have lower := small_probability W hW X D p v u ho minor hl smallChord φ phase Native.smallIntervals
        refine le_trans ?_ lower
        by_cases high : δ≤chord u v
        · rw [if_pos high,if_pos high]
          have h := mul_nonneg (nonnegative_cost p) (sub_nonneg.mpr (high.trans chordArc))
          exact div_le_div_of_nonneg_right (sub_le_self _ h) (by norm_num)
        · rw [if_neg high,if_neg high]
          have h := mul_nonneg (nonnegative_cost p) (sub_nonneg.mpr (hℓ.trans chordArc))
          exact div_le_div_of_nonneg_right (sub_le_self _ h) (by norm_num)
      · have above := lt_of_not_ge smallChord
        obtain ⟨i,a,b⟩ := medium_interval above range
        let fine := decide (p=Profile.fine)
        have checked : mediumCheck fine = true := by
          cases p
          · exact Native.mediumCoarse
          · exact Native.mediumFine
        have lower := medium_probability W hW X D p v u ho minor hl above φ phase fine i a b checked
        refine le_trans ?_ lower
        rw [if_pos (show δ≤chord u v by unfold δ; linarith)]
        have term : (mTarget fine (breakpoint i.val):ℝ) =
            intercept p-angleCost p*((breakpoint i.val:ℝ)-δ) := by
          cases p <;> norm_num [mTarget,fine,intercept,angleCost,delta,δ,show Profile.coarse ≠ Profile.fine by decide,show Profile.fine ≠ Profile.coarse by decide]
        rw [term]
        have h := mul_le_mul_of_nonneg_left
          (sub_le_sub_right (a.le.trans chordArc) δ) (nonnegative_cost p)
        exact div_le_div_of_nonneg_right (sub_le_sub_left h _) (by norm_num)
    · exact (outside p (show 245/1000 ≤ arcLength X u v by
        have := notMinor_pi_le minor; linarith [Real.pi_gt_three])).trans measureReal_nonneg
  · exact (outside p ((le_of_not_ge range).trans chordArc)).trans measureReal_nonneg

end HadwigerNelson.Centres.Events
