import HadwigerNelson.Forest.Credits
import HadwigerNelson.Blueprint.Point.Holes
import HadwigerNelson.Blueprint.Point.CentreEvents
import HadwigerNelson.Forest.CollisionCounts
import HadwigerNelson.Forest.CollisionAngles
import HadwigerNelson.Forest.Head
import HadwigerNelson.Forest.ShortMean
import HadwigerNelson.Forest.UnitMean
import HadwigerNelson.Forest.Potential
import HadwigerNelson.Forest.TwoTails

namespace HadwigerNelson.Forest
open MeasureTheory Set
open scoped BigOperators
open Centres Crossings
noncomputable section
attribute [local instance] Classical.propDecidable
local notation "Ωfn" => (ℝ → ℝ → ℝ)

/-- Lemma 34. Both lower bounds refer to the same physical translation law. -/
theorem blank_credit_lower (W : Wave.Datum) (Ω : Ωfn) (sound : Wave.holeEnclosure W Ω) :
    (∀ (ρ : ℝ) (v : Plane), 0 < ‖v‖ → ‖v‖ ≤ 2*ρ →
      lowerShort Ω ρ (shortIndex v) ≤ Wave.bothBlank W v) ∧
    (∀ t : ℝ, |t| ≤ w → unitCredit Ω t ≤ Wave.bothBlank W (Wave.point (Real.sin t) (Real.cos t))) :=
  blank_credits_from_holes W Ω sound (Wave.hole_covariogram_bounds W).2.2

/-- Lemma 35. The strict subset-edge criterion gives acyclicity of the
underlying undirected forest, including prohibition of two opposite edges. -/
theorem candidates_acyclic (X : Finset Plane) (L : Layers X) (m : Mode) (p : Profile) (θ : ℝ) :
    (∀ x ∈ X, ∀ y ∈ X, allCandidates L m p θ x y →
      rootHeight L θ x < rootHeight L θ y ∨
        (rootHeight L θ x = rootHeight L θ y ∧ depth L x < depth L y)) ∧
    (∀ F : Finset (Plane×Plane), (∀ z ∈ F, z.1 ∈ X ∧ z.2 ∈ X ∧ allCandidates L m p θ z.1 z.2) →
      (∀ e ∈ F, ∀ f ∈ F, e.2 = f.2 → e = f) →
      ∀ A ⊆ X, A.Nonempty → (F.filter fun z => z.1 ∈ A ∧ z.2 ∈ A).card < A.card) := by
  refine ⟨fun _ hx _ hy => candidate_increases L m p θ hx hy,?_⟩
  intro F hf unique A hA hn
  have inc (e) (he : e ∈ F) := candidate_increases L m p θ (hf e he).1 (hf e he).2.1 (hf e he).2.2
  convert incoming_forest (rootHeight L θ) (depth L) F inc unique A hA hn using 3

/-- Lemma 36: distinct inner tails at a common candidate head. -/
theorem two_tails (W : Wave.Datum) (hW : partialProfile W) (D : Finset Plane)
    (sep : Packing.separated D δ) (x x' y : Plane) (hx : x ∈ D) (hx' : x' ∈ D)
    (ne : x ≠ x') (θ : ℝ) (h₁ : unitCandidate θ x y) (h₂ : unitCandidate θ x' y) :
    ∀ᵐ τ ∂Placement.translationLaw W,
      ¬(Placement.colour W (θ,τ) x = none ∧ Placement.colour W (θ,τ) x' = none) :=
  two_inner_tails W hW D sep x x' y hx hx' ne θ h₁ h₂

/-- Lemma 38 uses the event that there is an incoming blank pair. The forest
selects exactly one such pair whenever that event occurs. -/
theorem head_credit_lower (W : Wave.Datum) (hW : partialProfile W) (Ω : Ωfn)
    (sound : Wave.holeEnclosure W Ω) (X : Finset Plane) (L : Layers X) (m : Mode)
    (p : Profile) (θ : ℝ) (y : Plane) (hy : y ∈ X) :
    edgeShort L Ω m θ y + excessCredit L Ω m θ y - collisionLoss L Ω m θ y +
      (∑ v ∈ X, (Placement.translationLaw W).real (centreEvent W X L.D p θ v y)) ≤
    (Placement.translationLaw W).real {τ | ∃ x ∈ X, allCandidates L m p θ x y ∧
      Placement.colour W (θ,τ) x = none ∧ Placement.colour W (θ,τ) y = none} := by
  have credits := blank_credit_lower W Ω sound
  exact head_credit_from_geometry W hW Ω sound X L m p θ y hy credits.1 credits.2
    (fun _ _ hv hu => ((candidate_geometry _ _ _ _ _ _ hu).2.1 _ hv))
    (fun v => candidate_event W hW X L.D p θ v y)

/-- Lemma 39 for each actual short parent edge. -/
theorem short_credit_expectation (W : Wave.Datum) (Ω : Ωfn) (sound : Wave.holeEnclosure W Ω)
    (X : Finset Plane) (L : Layers X) (y : Plane) (hy : y ∈ X) (notRoot : y ∉ L.D) :
    let ρ := if y ∈ L.R then d else a
    lowerShortMean Ω ρ ≤ shortMean Ω ρ ∧
    (∫ θ, edgeShort L Ω .r θ y ∂(Placement.uniformInterval (2*Real.pi))) = shortMean Ω ρ :=
  averaged_short_parent W Ω sound X L y hy notRoot

/-- Lemma 40 sums both unit orientations and charges the endpoint degrees. -/
theorem unit_credit_expectation (W : Wave.Datum) (Ω : Ωfn) (sound : Wave.holeEnclosure W Ω)
    (X : Finset Plane) (L : Layers X) (m : Mode) (ordinaryMode : m ≠ .centresOnly) :
    unitMean Ω * max 0 ((unitEdgeCount X : ℝ) -
      (∑ v ∈ X, ((if v ∈ eligible L m then 0 else 1 : ℝ) + 1-retention Ω (headCap L Ω v)) *
        unitDegree X v / 2)) ≤
    ∫ θ, (∑ y ∈ X, excessCredit L Ω m θ y) ∂(Placement.uniformInterval (2*Real.pi)) :=
  expected_unit_credit W Ω sound X L m

/-- Lemma 41, for two tails incident to one unit-edge head. -/
theorem collision_upper (W : Wave.Datum) (Ω : Ωfn) (sound : Wave.holeEnclosure W Ω)
    (x x' y : Plane) (hne : x ≠ x') (hx : dist x y = 1) (hx' : dist x' y = 1) :
    (∫ θ, min (edgeUnit Ω θ x y) (edgeUnit Ω θ x' y) ∂(Placement.uniformInterval (2*Real.pi))) ≤
    unitBin 1 / Real.pi * ∑ k : Fin 16384, if dist x x' ≤ 2*unitBin (k.val+1)
      then unitStep Ω (k.val+1) else 0 :=
  collision_mean W Ω sound x x' y hne hx hx'

/-- Lemma 42 with Lemma 31 used in both packing estimates. -/
theorem collision_constants (W : Wave.Datum) (Ω : Ωfn) (sound : Wave.holeEnclosure W Ω)
    (X : Finset Plane) (L : Layers X) :
    let K := packingSum Ω (fun _ => True)
    let T := packingSum Ω (fun t => d < t)
    let U := 2*packingSum Ω (fun t => t ≤ d)
    let j := L.R.card-L.D.card
    2*unitBin 1 / Real.pi * (∑ k : Fin 16384, unitStep Ω (k.val+1) *
      neighbourPairs L.R L.D (unitBin (k.val+1))) ≤
      min (L.R.card*K) (min (L.R.card*T + j*U) (j*(2*K))) := by
  apply collision_of_degree_cap sound L
  intro k u hu
  apply Packing.pointwise_degree L.R u a _ (by norm_num [a,δR]) _ _ hu
  · unfold unitBin w; positivity
  · convert L.maximalR.2.1 using 1; unfold a; ring_nf

end
end HadwigerNelson.Forest
