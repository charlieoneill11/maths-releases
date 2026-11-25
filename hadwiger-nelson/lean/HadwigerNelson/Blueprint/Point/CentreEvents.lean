import HadwigerNelson.Centres.OrientationBudget
import HadwigerNelson.Centres.Credit
import HadwigerNelson.Centres.Events.Probability
import HadwigerNelson.Centres.Admissible
import HadwigerNelson.Centres.Events.CandidateEvent
import HadwigerNelson.Centres.BudgetDefs
import HadwigerNelson.Centres.Events.Definitions
import HadwigerNelson.Wave.Geometry.PartialProfile
import HadwigerNelson.Blueprint.Point.Budgets
import HadwigerNelson.Data.PartialWave
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import HadwigerNelson.Blueprint.Point.Holes

namespace HadwigerNelson.Centres
open MeasureTheory Set Crossings
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

/-- Lemma 47. The downward unit point is in the open minor arc, the head has
a unique centre tail, the vertical gain dominates both parent steps, and a
medium chord excludes every competing unit candidate. -/
theorem candidate_geometry (X D : Finset Plane) (p : Profile) (θ : ℝ) (v u : Plane)
    (cand : candidate X D p θ v u) :
    (∃ a ∈ X, ∃ b ∈ X, consecutive X u a b ∧ consecutive X v a b ∧
      inMinorInterior (Placement.rotate θ a) (Placement.rotate θ b) (Placement.rotate θ u)
        (Placement.rotate θ v) (Placement.rotate θ u-Wave.point 0 1)) ∧
    (∀ v', candidate X D p θ v' u → v'=v) ∧
    δR+δ < (Placement.rotate θ (u-v)) 1 ∧
    (2/100 < chord u v → ∀ x ∈ X, ¬ unitCandidate θ x u) := by
  exact candidate_geometry_proof X D p θ v u cand

/-- Lemma 48 gives the head-event disjointness required in Lemma 38. -/
theorem candidate_event (W : Wave.Datum) (hW : partialProfile W) (X D : Finset Plane)
    (p : Profile) (θ : ℝ) (v u : Plane) :
    ∀ᵐ τ ∂Placement.translationLaw W, τ ∈ centreEvent W X D p θ v u →
      Placement.colour W (θ,τ) u = none ∧ Placement.colour W (θ,τ) v = none ∧
      ∀ x ∈ X, unitCandidate θ x u → (Placement.colour W (θ,τ) x).isSome = true := by
  exact candidate_event_sound W X D p θ v u

/-- Lemma 49 averages over the rotation and translation of a fixed oriented pair. -/
theorem probability_lower (W : Wave.Datum) (hW : partialProfile W) (X D : Finset Plane)
    (p : Profile) (u v : Plane) (ho : orientation X D v u) (hℓ : δR ≤ chord u v) :
    let l := chord u v
    let z := arcLength X u v
    (if δ ≤ l then (intercept p-angleCost p*(z-δ))/2
      else (smallIntercept p-angleCost p*(z-δR))/2) ≤
      (Placement.law W).real {ω | ω.2 ∈ centreEvent W X D p ω.1 v u} := by
  exact Events.probability_lower W hW X D p u v ho hℓ

/-- Lemma 50, with the minimum of all three valid short-chord budgets. -/
theorem admissible_budgets (X R D : Finset Plane) (hR : Forest.maximalSeparated X R δR)
    (hD : Forest.maximalSeparated R D δ) (hd : minNonisolatedDegree X 3) :
    let s := X.card-R.card
    let j := R.card-D.card
    let LR : ℝ := outsideDegree X R
    let LD : ℝ := outsideDegree X D
    admissible X δR (min LR (min (5*s+s.choose 2 : ℕ) ((LR+5*s)/2))) ∧
    admissible X δ (min LD (min (14*s+8*j+s.choose 2 : ℕ) ((LD+5*(s+j))/2))) := by
  exact physical_admissible_budgets X R D hR hD

/-- Lemma 51 counts eligible orientations and charges excess arc length to
single chords at each of the seven thresholds. -/
theorem orientation_budgets (X D : Finset Plane) (hD : D ⊆ X) (sep : Packing.separated D δ)
    (hd : minNonisolatedDegree X 3) (bR bD : ℝ) (hR : admissible X δR bR)
    (hbD : admissible X δ bD) :
    let t : ℝ := doubledPairs X
    let LD : ℝ := outsideDegree X D
    t - bR - LD/2 ≤ ((orientationSet X D δR).card : ℝ)/2 ∧
    t - bD - LD/2 ≤ ((orientationSet X D δ).card : ℝ)/2 ∧
    (∑ z ∈ orientationSet X D δR, (arcLength X z.2 z.1 - if δ ≤ chord z.2 z.1 then δ else δR))/2 ≤
      angularBudget X.card (unitEdgeCount X) (doubledPairs X) (X.card-D.card) LD bR bD := by
  exact physical_orientation_budgets X D hD sep hd bR bD hR hbD

/-- Proposition 52 after the count, degree and admissible-budget substitutions.
The score is bounded by the expected number of actual centre events. -/
theorem credit_lower (facts : CitedFacts) (W : Wave.Datum) (hW : partialProfile W)
    (X R D : Finset Plane) (hn : 2090 ≤ X.card) (hd : minNonisolatedDegree X 3)
    (hR : Forest.maximalSeparated X R δR) (hD : Forest.maximalSeparated R D δ) (p : Profile) :
    profileCredit X.card (unitEdgeCount X) (X.card-R.card) (R.card-D.card)
      (intercept p) (smallIntercept p) (angleCost p) ≤
      ∑ z ∈ orientationSet X D δR, (Placement.law W).real
        {ω | ω.2 ∈ centreEvent W X D p ω.1 z.1 z.2} := by
  apply credit_from_estimates facts X R D hn hd hR hD p
  · intro z; exact measureReal_nonneg
  · intro z ho hc
    exact probability_lower W hW X D p z.2 z.1 ho hc
  · intro bR bD ar ad
    exact orientation_budgets X D (hD.1.trans hR.1) hD.2.1 hd bR bD ar ad

end
end HadwigerNelson.Centres
