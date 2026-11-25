import HadwigerNelson.Forest.Main
import HadwigerNelson.Blueprint.Point.Finite
import HadwigerNelson.Blueprint.Point.Boxes

namespace HadwigerNelson.Point
open scoped BigOperators

open Crossings
attribute [local instance] Classical.propDecidable

/-- A finite configuration can be enlarged by a point farther than one from
every old vertex. One coordinate larger than the sum of all norms suffices. -/
theorem exists_far (X : Finset Plane) : ∃ p : Plane, ∀ x ∈ X, 1 < dist p x := by
  let R := ∑ x ∈ X, ‖x‖
  let p : Plane := PiLp.single 2 (0 : Fin 2) (R+2 : ℝ)
  have hR : 0 ≤ R := Finset.sum_nonneg fun x _ => norm_nonneg x
  have hp : ‖p‖ = R+2 := by simp [p, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R+2)]
  refine ⟨p, ?_⟩
  intro x hx
  have hxR : ‖x‖ ≤ R := Finset.single_le_sum (fun y _ => norm_nonneg y) hx
  have tri := dist_triangle p x 0
  rw [dist_zero_right, dist_zero_right, hp] at tri
  linarith

private theorem insert_far {X : Finset Plane} {p : Plane} (hp : ∀ x ∈ X, 1 < dist p x)
    {d : ℕ} (hX : minNonisolatedDegree X d) : minNonisolatedDegree (insert p X) d := by
  classical
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · left
    simp only [unitDegree, Finset.filter_insert, dist_self, zero_ne_one, ↓reduceIte]
    apply Finset.card_eq_zero.mpr
    exact Finset.filter_eq_empty_iff.mpr fun y hy => (hp y hy).ne'
  · have hpx : dist x p ≠ 1 := by rw [dist_comm]; exact (hp x hx).ne'
    simpa [unitDegree, Finset.filter_insert, hpx] using hX x hx

/-- The standard critical-subset and isolated-vertex reduction at the start of §9. -/
theorem padded_counterexample (X : Finset Plane) (N : ℕ) (hN : X.card ≤ N)
    (bad : ¬ Colourable (fun x y : Plane => dist x y = 1) X) :
    ∃ Z : Finset Plane, Z.card = N ∧ ¬ Colourable (fun x y : Plane => dist x y = 1) Z ∧
      minNonisolatedDegree Z 6 := by
  classical
  let adj := fun x y : Plane => dist x y = 1
  obtain ⟨Y,hYX,hbad,hdeg⟩ := critical_subset adj (fun _ _ h => (dist_comm _ _).trans h)
    (fun x => by simp [adj]) X bad
  have grow (t : ℕ) : ∃ Z : Finset Plane,
      Z.card = Y.card + t ∧ ¬ Colourable adj Z ∧ minNonisolatedDegree Z 6 := by
    induction t with
    | zero => exact ⟨Y,by simp,hbad,fun x hx => Or.inr (hdeg x hx)⟩
    | succ t ih =>
      obtain ⟨S,hS,hc,hd⟩ := ih
      obtain ⟨p,hp⟩ := exists_far S
      have fresh : p ∉ S := by
        intro hm
        have impossible := hp p hm
        rw [dist_self] at impossible
        linarith
      refine ⟨insert p S, by rw [Finset.card_insert_of_notMem fresh,hS]; omega, ?_, insert_far hp hd⟩
      intro coloured
      obtain ⟨c,h⟩ := coloured
      exact hc ⟨c, fun x hx y hy => h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)⟩
  have leN := (Finset.card_le_card hYX).trans hN
  obtain ⟨Z,hc,hb,hd⟩ := grow (N-Y.card)
  exact ⟨Z,by omega,hb,hd⟩

private theorem layers (X : Finset Plane) (δ : ℝ) : ∃ P, Forest.maximalSeparated X P δ := by
  have sym : Symmetric (fun x y : Plane => δ < dist x y) := by
    intro x y h
    simpa [dist_comm y x] using h
  obtain ⟨P,sub,apart,covered⟩ := maximal_layer X _ sym
  refine ⟨P,sub,apart,?_⟩
  intro x hx hp
  obtain ⟨y,hy,near⟩ := covered x hx hp
  exact ⟨y,hy,le_of_not_gt near⟩

/-- Theorem 1 follows from the point blueprint's one geometric lower bound on
the objective, its finite upper bound, and the degree-variance edge ceiling. -/
theorem six_colour_of_point_estimates (facts : CitedFacts) (X : Finset Plane) (hX : X.card ≤ 10689) :
    Colourable (fun x y : Plane => dist x y = 1) X := by
  by_contra bad
  obtain ⟨Z,hn,hbad,hd⟩ := padded_counterexample X 10689 hX bad
  obtain ⟨R,hR⟩ := layers Z (53/10000)
  obtain ⟨D,hD⟩ := layers R (1837/250000)
  have hRcard := Finset.card_le_card hR.1
  have hDcard := Finset.card_le_card hD.1
  have lower := Forest.main_inequality facts Z R D (by omega) hd hbad hR hD
  rw [hn] at lower
  have upper := Certificate.point_bound_lt_one (unitEdgeCount Z) (10689-R.card) (R.card-D.card)
    (edge_ceiling facts Z hn (fun x hx => (hd x hx).imp_right (by omega))) (by omega)
  exact (not_lt_of_ge lower) upper

end HadwigerNelson.Point
