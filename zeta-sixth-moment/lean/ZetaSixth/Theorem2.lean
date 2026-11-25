import ZetaSixth.Projection
import ZetaSixth.RegionMasses

namespace ZetaSixth

open Filter MeasureTheory

/-- Theorem 2 conditional on the paper's analytic pairings. -/
theorem main_of (h : PaperPairings) (c : ℝ) (hc : c < (C : ℝ)) :
    ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T :=
  main_of_mass mu_U7 h c hc

/-- The exact numerical projection ceiling for profiles in the supports of Proposition 3. -/
theorem projection_ceiling_exact (𝒯 : Family) (V : Profile)
    (hV : (V : Point → ℝ) =ᵐ[chamberVolume] v)
    (hSupp : ∀ (B : Test) (g : Profile), (B, g) ∈ 𝒯 →
      ∀ᵐ p ∂chamberVolume, p ∉ ceiling → g p = 0) :
    (Nat.factorial 9 : ℝ) * ‖(familySpan 𝒯).starProjection V‖ ^ 2 ≤ (ceilingMass : ℝ) := by
  have hNonneg : 0 ≤ (ceilingMass : ℝ) := by norm_num [ceilingMass]
  have h := projection_ceiling 𝒯 V hV hSupp
  simpa only [mu_ceiling, ENNReal.toReal_ofReal hNonneg] using h

end ZetaSixth
