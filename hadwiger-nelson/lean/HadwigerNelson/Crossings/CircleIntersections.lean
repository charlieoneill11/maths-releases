import HadwigerNelson.Plane
import Mathlib.Geometry.Euclidean.Basic

namespace HadwigerNelson.Crossings

/-- Distinct unit circles in the plane meet in a finite set of at most two points. -/
theorem unit_intersections_le_two (a b : Plane) (hab : a ≠ b) :
    ∃ T : Finset Plane, T.card ≤ 2 ∧ ∀ z, z ∈ T ↔ dist z a = 1 ∧ dist z b = 1 := by
  classical
  let P (x : Plane) := dist x a = 1 ∧ dist x b = 1
  by_cases first : ∃ x, P x
  · obtain ⟨x,hx⟩ := first
    by_cases second : ∃ y, P y ∧ x ≠ y
    · obtain ⟨y,hy,hxy⟩ := second
      refine ⟨{x,y},by simp [hxy],?_⟩
      intro z
      simp only [Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro (rfl|rfl) <;> assumption
      · intro hz
        exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
          (V := Plane) finrank_euclideanSpace_fin hab hxy hx.1 hy.1 hz.1 hx.2 hy.2 hz.2
    · refine ⟨{x},by simp,?_⟩
      intro z
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl; exact hx
      · intro hz
        by_contra h
        exact second ⟨z,hz,Ne.symm h⟩
  · exact ⟨∅,by simp,fun z => ⟨by simp,fun hz => (first ⟨z,hz⟩).elim⟩⟩

end HadwigerNelson.Crossings
