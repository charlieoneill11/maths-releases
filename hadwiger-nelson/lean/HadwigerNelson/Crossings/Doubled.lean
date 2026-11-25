import HadwigerNelson.Crossings.DoubleCount
import HadwigerNelson.Crossings.VertexSample
import HadwigerNelson.Crossings.UniformSubset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Lemma 45. The simple graph of retained circle arcs obeys the sampled
crossing inequality, while all circle crossings share the budget remaining
after accounting for marked unit neighbours. -/

namespace HadwigerNelson.Crossings
noncomputable section
open Finset Centres

private theorem arc_crossings_upper (X : Finset Plane) (hn : 0 < X.card) (A : UnitArcDrawing X) :
    (A.D.crossingCount : ℝ) ≤ (X.card : ℝ)*(X.card-1 : ℝ) + (unitEdgeCount X : ℝ) -
      2*(unitEdgeCount X : ℝ)^2/X.card := by
  let n : ℝ := X.card
  let m : ℝ := unitEdgeCount X
  let d (x : Plane) : ℝ := unitDegree X x
  have hn' : 0<n := by dsimp [n]; exact_mod_cast hn
  have sumdeg : ∑ x ∈ X, d x = 2*m := by dsimp [d,m]; exact_mod_cast sum_unitDegree X
  have cs := sum_mul_sq_le_sq_mul_sq X (fun _ => (1:ℝ)) d
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sumdeg] at cs
  have hs : (2*m)^2/n ≤ ∑ x ∈ X, (d x)^2 := (div_le_iff₀ hn').mpr (by simpa only [mul_comm] using cs)
  have expand (x : Plane) : (d x)^2 = 2*((unitDegree X x).choose 2 : ℝ) + d x := by
    rw [Nat.cast_choose_two]; dsimp [d]; ring
  simp_rw [expand,sum_add_distrib,←mul_sum,sumdeg] at hs
  have upper : (A.D.crossingCount : ℝ) + (∑ x ∈ X, ((unitDegree X x).choose 2 : ℝ)) ≤ 2*(X.card.choose 2 : ℝ) := by
    exact_mod_cast A.crossing_and_marked
  rw [Nat.cast_choose_two ℝ X.card] at upper
  change (A.D.crossingCount : ℝ) ≤ n*(n-1)+m-2*m^2/n
  change _ ≤ 2*(n*(n-1)/2) at upper
  simp only [div_eq_mul_inv] at hs ⊢
  linear_combination hs/2 + upper

private theorem retained_bound (facts : CitedFacts) (X : Finset Plane) (hn : 1317 ≤ X.card)
    (A : UnitArcDrawing X) : ((arcSlot A.G false).card : ℤ) ≤ retainedArcBound X.card (unitEdgeCount X) := by
  let S := arcSlot A.G false
  let s := Selection.spanning A.G S
  let D := s.drawing A.D
  have simple := arcSlot_simple A.G A.multiplicity_le_two false
  have hk : 4 ≤ 1317 := by decide
  have sample := vertex_sample_bound facts s.graph simple hk hn (fun W h => count_supersets W h hn)
    (pair_count hk hn) (four_count hk hn)
  have draw := facts.le_drawing s.graph simple D (s.finite A.D A.finite_intersections)
  have kept : D.crossingCount ≤ A.D.crossingCount := by
    simpa [D] using
      s.count_le_filter A.D A.finite_intersections (fun _ => True) (fun _ => trivial)
  have num : sampledLower X.card 1317 S.card ≤ (A.D.crossingCount : ℝ) :=
    sample.trans (by exact_mod_cast draw.trans kept)
  have upper := arc_crossings_upper X (by omega) A
  have hp := fourProbability_pos hk hn
  have hn' : (1317:ℝ) ≤ X.card := by exact_mod_cast hn
  have pp : 0 < pairProbability X.card 1317 := by
    unfold pairProbability
    exact div_pos (by norm_num) (mul_pos (by linarith) (by linarith))
  rw [sampledLower,div_le_iff₀ hp] at num
  rw [retainedArcBound,Int.le_floor,Int.cast_natCast,le_div_iff₀ (mul_pos (by norm_num) pp)]
  have bound := mul_le_mul_of_nonneg_right upper hp.le
  change (S.card : ℝ) * _ ≤ _
  norm_num at num ⊢
  linarith only [num,bound]

theorem doubled_pairs_lower_bound (facts : CitedFacts) (X : Finset Plane)
    (hn : 1317 ≤ X.card) (hd : minNonisolatedDegree X 3) :
    2*(unitEdgeCount X : ℤ) - retainedArcBound X.card (unitEdgeCount X) ≤ doubledPairs X := by
  let A := CircleDrawing.unitDrawing X hd
  have kept := retained_bound facts X hn A
  have lost := discarded_le_doubled X hd
  change (arcSlot A.G true).card ≤ doubledPairs X at lost
  have total := arcSlot_sum A.G
  omega

end
end HadwigerNelson.Crossings
