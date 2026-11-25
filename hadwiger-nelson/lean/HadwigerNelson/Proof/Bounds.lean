import HadwigerNelson.Cited
import HadwigerNelson.Blueprint.Edge
import HadwigerNelson.Blueprint.Point.Assembly
import Mathlib.Data.Finset.Card

/-! Implementations of the approved finite graph bounds. -/
namespace HadwigerNelson.Proof

theorem edges (E : Finset (Plane × Plane)) (hE : ∀ e ∈ E, dist e.1 e.2 = 1)
    (hcard : E.card ≤ 245510) :
    ∃ c : Plane → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2 :=
  complete_edge_bound E hE hcard

theorem points (h : CitedFacts) (X : Finset Plane) (hX : X.card ≤ 10689) :
    ∃ c : Plane → Fin 6, ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → c x ≠ c y :=
  Point.six_colour_of_point_estimates h X hX

end HadwigerNelson.Proof
