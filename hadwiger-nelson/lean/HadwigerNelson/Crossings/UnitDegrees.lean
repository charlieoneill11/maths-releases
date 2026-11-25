import HadwigerNelson.Crossings.Parameters
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination

namespace HadwigerNelson.Crossings
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def unitDegree (X : Finset Plane) (x : Plane) : ℕ := by
  classical exact (X.filter fun y => dist x y = 1).card

def unitEdgeCount (X : Finset Plane) : ℕ :=
  (∑ x ∈ X, unitDegree X x) / 2

def minNonisolatedDegree (X : Finset Plane) (d : ℕ) : Prop :=
  ∀ x ∈ X, unitDegree X x = 0 ∨ d ≤ unitDegree X x

def varianceBound (n k : ℕ) (m : ℝ) : ℝ :=
  (n : ℝ) * (n - 1 : ℝ) - 4 * sampledLower n k m - 2 * m ^ 2 / n + m

/-- Adding a vertex increases the total degree by twice its number of old neighbours. -/
theorem sum_unitDegree (X : Finset Plane) : ∑ x ∈ X, unitDegree X x = 2*unitEdgeCount X := by
  classical
  have ev : Even (∑ x ∈ X, unitDegree X x) := by
    induction X using Finset.induction_on with
    | empty => simp
    | @insert v X hv ih =>
      have insertDegree (y : Plane) : unitDegree (insert v X) y =
          unitDegree X y + (if dist y v = 1 then 1 else 0) := by
        by_cases h : dist y v = 1
        · simp [unitDegree, Finset.filter_insert, h, hv]
        · simp [unitDegree, Finset.filter_insert, h]
      have sumNew : (∑ y ∈ X, if dist y v = 1 then 1 else 0) = unitDegree X v := by
        unfold unitDegree
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro y _
        rw [dist_comm v y]
      obtain ⟨q,hq⟩ := ih
      refine ⟨q+unitDegree X v,?_⟩
      rw [Finset.sum_insert hv]
      simp_rw [insertDegree,Finset.sum_add_distrib]
      rw [sumNew,hq]
      simp only [dist_self,zero_ne_one,if_false,add_zero]
      omega
  obtain ⟨q,hq⟩ := ev
  unfold unitEdgeCount
  omega

/-- The variance identity which converts the count of crossings and marked circle
intersections into Lemma 29. -/
theorem variance_from_pairs (X : Finset Plane) (k : ℕ) (hn : 0 < X.card)
    (bound : 4*sampledLower X.card k (unitEdgeCount X) +
      (∑ x ∈ X, ((unitDegree X x).choose 2 : ℝ)) ≤ (X.card : ℝ)*(X.card-1 : ℝ)) :
    (∑ x ∈ X, ((unitDegree X x : ℝ) - 2*(unitEdgeCount X : ℝ)/X.card)^2) ≤
      2*varianceBound X.card k (unitEdgeCount X) := by
  let d := fun x ↦ (unitDegree X x : ℝ)
  let n := (X.card : ℝ)
  let m := (unitEdgeCount X : ℝ)
  have hp : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hs : (∑ x ∈ X, d x) = 2*m := by dsimp [d,m]; exact_mod_cast sum_unitDegree X
  have eq (x : Plane) : (d x-2*m/n)^2 =
      2*((unitDegree X x).choose 2 : ℝ) + (1-4*m/n)*d x + (2*m/n)^2 := by
    rw [Nat.cast_choose_two]; dsimp [d]; ring
  change (∑ x ∈ X, (d x-2*m/n)^2) ≤ 2*(n*(n-1)-4*sampledLower X.card k m-2*m^2/n+m)
  simp_rw [eq,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,hs]
  change _ + n*(2*m/n)^2 ≤ _
  have alg : (1-4*m/n)*(2*m) + n*(2*m/n)^2 = 2*m-4*m^2/n := by
    field_simp [hp.ne']; ring
  rw [add_assoc,alg]
  change 4*sampledLower X.card k m + _ ≤ n*(n-1) at bound
  linear_combination 2 * bound

end
end HadwigerNelson.Crossings
