import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FunProp

namespace HadwigerNelson.Packing
open Set

private theorem nonneg_of_deriv {f g : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (g x) x)
    (h0 : 0 ≤ f 0) (hg : ∀ x, 0 ≤ x → 0 ≤ g x) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun z ↦ (hf z).continuousAt
  have mono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ)) hc.continuousOn
    (fun z _ ↦ (hf z).hasDerivWithinAt) (fun z hz ↦ hg z (interior_subset hz))
  exact h0.trans (mono (Set.mem_Ici.mpr (le_refl (0:ℝ))) hx hx)

/-- Sixth-order lower bound on cosine used for the outward angular tests. -/
theorem cosine_poly (x : ℝ) (hx : 0 ≤ x) :
    1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  have p3 (z : ℝ) (hz : 0 ≤ z) : 0 ≤ Real.sin z-z+z^3/6 := by
    apply nonneg_of_deriv (g := fun t ↦ Real.cos t-1+t^2/2) _ (by norm_num) _ z hz
    · intro t
      convert ((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).add
        (((hasDerivAt_id t).pow 3).div_const 6) using 1 <;> simp <;> ring
    · intro t _; linarith [Real.one_sub_sq_div_two_le_cos (x:=t)]
  have p2 (z : ℝ) (hz : 0 ≤ z) : 0 ≤ -Real.cos z+1-z^2/2+z^4/24 := by
    apply nonneg_of_deriv (g := fun t ↦ Real.sin t-t+t^3/6) _ (by norm_num) p3 z hz
    intro t
    convert ((((Real.hasDerivAt_cos t).neg.add_const 1).sub
      (((hasDerivAt_id t).pow 2).div_const 2)).add (((hasDerivAt_id t).pow 4).div_const 24)) using 1 <;> simp <;> ring
  have p1 (z : ℝ) (hz : 0 ≤ z) : 0 ≤ -Real.sin z+z-z^3/6+z^5/120 := by
    apply nonneg_of_deriv (g := fun t ↦ -Real.cos t+1-t^2/2+t^4/24) _ (by norm_num) p2 z hz
    intro t
    convert ((((Real.hasDerivAt_sin t).neg.add (hasDerivAt_id t)).sub
      (((hasDerivAt_id t).pow 3).div_const 6)).add (((hasDerivAt_id t).pow 5).div_const 120)) using 1 <;> simp <;> ring
  have p0 : 0 ≤ Real.cos x-1+x^2/2-x^4/24+x^6/720 := by
    apply nonneg_of_deriv (g := fun t ↦ -Real.sin t+t-t^3/6+t^5/120) _ (by norm_num) p1 x hx
    intro t
    convert (((((Real.hasDerivAt_cos t).sub_const 1).add (((hasDerivAt_id t).pow 2).div_const 2)).sub
      (((hasDerivAt_id t).pow 4).div_const 24)).add (((hasDerivAt_id t).pow 6).div_const 720)) using 1 <;> simp <;> ring
  linarith

end HadwigerNelson.Packing
