import HadwigerNelson.Crossings.Variance
import HadwigerNelson.Crossings.CircleDrawing
import HadwigerNelson.Packing.Pointwise
import HadwigerNelson.Packing.ClosePairs
import HadwigerNelson.Crossings.Weighted
import HadwigerNelson.Crossings.VertexSample
import HadwigerNelson.Crossings.UniformSubset
import HadwigerNelson.Crossings.Halving
import HadwigerNelson.Crossings.Parameters
import HadwigerNelson.Cited
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The conditional point argument, §§5–9 of the paper. The geometric graph
below contains every unit pair, including those on circles about other vertices. -/

namespace HadwigerNelson

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Crossings

/-- Theorem 26 with denominators cleared. -/
theorem linear_lower (facts : CitedFacts) {n m : ℕ} (G : Graph n m)
    (simple : G.IsSimple) (hn : 3 ≤ n) :
    54 * (m : ℤ) - 266 * ((n : ℤ) - 2) ≤ 9 * (crossingNumber G : ℤ) :=
  improved_lower facts G simple hn

/-- Lemma 27 samples induced subgraphs of an optimal good drawing. -/
theorem sample_lower (facts : CitedFacts) {n m k : ℕ} (G : Graph n m)
    (simple : G.IsSimple) (hk : 4 ≤ k) (hkn : k ≤ n) :
    0 < fourProbability n k ∧ sampledLower n k m ≤ crossingNumber G := by
  exact ⟨fourProbability_pos hk hkn, vertex_sample_bound facts G simple hk hkn
    (fun W h ↦ count_supersets W h hkn) (pair_count hk hkn) (four_count hk hkn)⟩

/-- Lemma 28 applies to the given drawing, including drawings of multigraphs. -/
theorem halving (facts : CitedFacts) {n m k : ℕ} (G : Graph n (2 * m)) (D : Drawing G)
    (hk : 4 ≤ k) (hkn : k ≤ n) (hm : ∀ v w, multiplicity G v w ≤ 2)
    (hD : D.FiniteIntersections) : 4 * sampledLower n k m ≤ D.crossingCount :=
  half_from_sample facts G D hk hkn hm hD (fun g h ↦ (sample_lower facts g h hk hkn).2)

/-- Lemma 29 uses the drawing whose arcs join consecutive marked points on
each unit circle. The degree hypothesis rules out a parallel pair on one circle. -/
theorem degree_variance (facts : CitedFacts) (X : Finset Plane) (k : ℕ)
    (hk : 4 ≤ k) (hn : k ≤ X.card) (hd : minNonisolatedDegree X 3) :
    (∑ x ∈ X, ((unitDegree X x : ℝ) - 2 * (unitEdgeCount X : ℝ) / X.card) ^ 2) ≤
      2 * varianceBound X.card k (unitEdgeCount X) := by
  let A := CircleDrawing.unitDrawing X hd
  apply degree_variance_of_drawing X k (by omega) A
  exact halving facts A.G A.D hk hn A.multiplicity_le_two A.finite_intersections

/-- The strict sign change in Corollary 30 is rational arithmetic. -/
theorem ceiling_signs :
    0 < varianceBound 10689 2090 403078 ∧ varianceBound 10689 2090 403079 < 0 := by
  norm_num [varianceBound, sampledLower, pairProbability, fourProbability]

private theorem above_ceiling (m : ℕ) (hm : 403079 ≤ m) :
    varianceBound 10689 2090 m < 0 := by
  have h : (403079 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : (403079 : ℝ)^2 ≤ (m : ℝ)^2 :=
    pow_le_pow_left₀ (by norm_num) h 2
  norm_num [varianceBound, sampledLower, pairProbability, fourProbability]
  nlinarith

theorem edge_ceiling (facts : CitedFacts) (X : Finset Plane)
    (hn : X.card = 10689) (hd : minNonisolatedDegree X 3) : unitEdgeCount X ≤ 403078 := by
  have h := degree_variance facts X 2090 (by decide) (by omega) hd
  have hsum : 0 ≤ ∑ x ∈ X, ((unitDegree X x : ℝ) - 2 * (unitEdgeCount X : ℝ) / X.card) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv := hsum.trans h
  rw [hn] at hv
  by_contra! hm
  have hneg := above_ceiling (unitEdgeCount X) hm
  linarith

theorem weighted_degree_upper (facts : CitedFacts) (X S J : Finset Plane) (α β : ℝ)
    (hn : 2090 ≤ X.card) (hd : minNonisolatedDegree X 3) (hS : S ⊆ X) (hJ : J ⊆ X)
    (hSJ : Disjoint S J) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    α * (∑ x ∈ S, (unitDegree X x : ℝ)) + β * (∑ x ∈ J, (unitDegree X x : ℝ)) ≤
      weightedBound X.card (unitEdgeCount X) S.card J.card α β := by
  exact weighted_of_variance X S J α β (by omega) hS hJ hSJ
    (degree_variance facts X 2090 (by decide) hn hd)

end Crossings

namespace Packing

theorem pointwise_degree (P : Finset Plane) (z : Plane) (ρ t : ℝ)
    (hρ : 0 < ρ) (ht : 0 < t) (hP : separated P (2*ρ)) (hz : z ∈ P) :
    nearDegree P z t ≤ neighbourCap ρ t :=
  near_degree_bound P z ρ t hρ ht hP hz

/-- Lemma 33 for the two radii used by the point certificate. -/
theorem close_pairs (X R D : Finset Plane) (hR : R ⊆ X) (hD : D ⊆ R)
    (sepR : separated R (53/10000)) (sepD : separated D (1837/250000)) :
    let s := X.card - R.card
    let j := R.card - D.card
    shortPairs X (53/10000) ≤ 5*s + s.choose 2 ∧
      shortPairs X (1837/250000) ≤ 14*s + 8*j + s.choose 2 :=
  close_pairs_bound X R D hR hD sepR sepD

end Packing

end
end HadwigerNelson
