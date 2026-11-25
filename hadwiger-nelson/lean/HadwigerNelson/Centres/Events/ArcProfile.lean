import HadwigerNelson.Centres.Parameters
import HadwigerNelson.Forest.FoldedAngles

namespace HadwigerNelson.Centres
open Placement Wave
noncomputable section

theorem exists_aligned_phase (u v : Plane) : ∃ φ : ℝ, ∀ t, aligned (t-φ) t v u := by
  obtain ⟨α,h⟩ := Forest.rotated_components (u-v)
  refine ⟨α-Real.pi/2,fun t => ?_⟩
  unfold aligned
  rw [h,show t-(α-Real.pi/2)+α=t+Real.pi/2 by ring,Real.cos_add_pi_div_two,Real.sin_add_pi_div_two,
    dist_eq_norm]
  ext i; fin_cases i <;> rfl

theorem notMinor_pi_le {X : Finset Plane} {u v : Plane} (hm : ¬minorArc X u v) :
    Real.pi ≤ arcLength X u v := by
  rw [arcLength,if_neg hm]
  linarith [Real.arcsin_le_pi_div_two (chord u v/2)]

theorem chord_le_arcLength (X : Finset Plane) (u v : Plane) : chord u v ≤ arcLength X u v := by
  have h0 : 0≤chord u v := Real.sqrt_nonneg _
  have h2 : chord u v≤2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith [sq_nonneg (dist u v)]⟩
  by_cases minor : minorArc X u v
  · rw [arcLength,if_pos minor]
    have h := Real.sin_le (Real.arcsin_nonneg.mpr (by linarith : 0≤chord u v/2))
    rw [Real.sin_arcsin (by linarith) (by linarith)] at h
    linarith
  · exact h2.trans ((by linarith [Real.pi_gt_three] : (2:ℝ)≤Real.pi).trans (notMinor_pi_le minor))

end
end HadwigerNelson.Centres
