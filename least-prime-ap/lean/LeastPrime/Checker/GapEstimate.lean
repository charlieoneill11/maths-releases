import LeastPrime.Checker.GapGeometry
import LeastPrime.Checker.Quadrature

/-! The rounded integral contribution on a level-two cell. -/

namespace LeastPrime.Checker

open MeasureTheory Set

theorem lower_cell_estimate {T : GridSet} {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hGood : ∀ I ∈ T, Good I) (hDesc : T.Pairwise fun I J => J.2 < I.1)
    (hBelow : ∀ I ∈ T, I.2 ≤ a)
    (hCuts : ∀ c ∈ breakpointCandidates .lower T, ¬ (a < c ∧ c < b)) :
    grid (b - a) * grid (estimatedProbability .lower a b
      (availableLength .lower T a) (availableLength .lower T b)) ≤
      ∫ r in Icc (grid a) (grid b), gLower r (denote T) / r := by
  obtain ⟨α, β, hAffine⟩ := gLower_affine_between_cuts hGood hDesc hCuts
  have hBelowB : ∀ I ∈ T, I.2 ≤ b := fun I hI => (hBelow I hI).trans hab.le
  have hSound := (estimatedProbability_bounds ha hab hAffine
    (grid_availableLength_lower hGood hDesc hBelow).symm
    (grid_availableLength_lower hGood hDesc hBelowB).symm).1
  simpa only [grid_sub hab.le] using hSound

theorem upper_cell_estimate {T : GridSet} {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hGood : ∀ I ∈ T, Good I) (hDesc : T.Pairwise fun I J => J.2 < I.1)
    (hBelow : ∀ I ∈ T, I.2 ≤ a)
    (hCuts : ∀ c ∈ breakpointCandidates .upper T, ¬ (a < c ∧ c < b)) :
    (∫ r in Icc (grid a) (grid b), gUpper r (denote T) / r) ≤
      grid (b - a) * grid (estimatedProbability .upper a b
        (availableLength .upper T a) (availableLength .upper T b)) := by
  obtain ⟨α, β, hAffine⟩ := gUpper_affine_between_cuts hGood hDesc hCuts
  have hBelowB : ∀ I ∈ T, I.2 ≤ b := fun I hI => (hBelow I hI).trans hab.le
  have hSound := (estimatedProbability_bounds ha hab hAffine
    (grid_availableLength_upper hGood hDesc hBelow).symm
    (grid_availableLength_upper hGood hDesc hBelowB).symm).2
  simpa only [grid_sub hab.le] using hSound

end LeastPrime.Checker
