import HadwigerNelson.Proof.Bounds
import HadwigerNelson.Sanity

/-! The plane is `EuclideanSpace ℝ (Fin 2)`. An edge is an ordered pair
of its endpoints, so an undirected graph can be listed by choosing either
orientation of each edge. Isolated vertices impose no colouring constraint. -/
namespace HadwigerNelson

/-- Theorem 2. At most 245,510 unit segments admit a proper six-colouring. -/
theorem edges_le_245510 (E : Finset (Plane × Plane)) (hE : ∀ e ∈ E, dist e.1 e.2 = 1)
    (hcard : E.card ≤ 245510) :
    ∃ c : Plane → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2 :=
  Proof.edges E hE hcard

/-- Theorem 1 as an unconditional target proposition. -/
def points_le_10689 : Prop :=
  ∀ (X : Finset Plane), X.card ≤ 10689 →
    ∃ c : Plane → Fin 6, ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → c x ≠ c y

/-- Theorem 1 under the graph-drawing results listed in `CitedFacts`. -/
theorem points_le_10689_of_cited (h : CitedFacts) (X : Finset Plane) (hX : X.card ≤ 10689) :
    ∃ c : Plane → Fin 6, ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → c x ≠ c y :=
  Proof.points h X hX

/-- A 3–4–5 displacement measures one in the Euclidean metric. -/
theorem dist_three_fifths_four_fifths :
    dist (!₂[0, 0] : Plane) !₂[3 / 5, 4 / 5] = 1 :=
  Sanity.dist_three_fifths_four_fifths

/-- The explicit triangle has three unit sides. -/
theorem unit_triangle_side_lengths :
    dist (!₂[0, 0] : Plane) !₂[1, 0] = 1 ∧
    dist (!₂[0, 0] : Plane) !₂[1 / 2, Real.sqrt 3 / 2] = 1 ∧
    dist (!₂[1, 0] : Plane) !₂[1 / 2, Real.sqrt 3 / 2] = 1 :=
  Sanity.unit_triangle_side_lengths

/-- The three points (0,0), (1,0), (1/2,√3/2) do not admit a proper two-colouring. -/
theorem unit_triangle_no_two_colouring :
    ¬ ∃ c : Plane → Fin 2,
      ∀ x ∈ Sanity.unitTriangle, ∀ y ∈ Sanity.unitTriangle, dist x y = 1 → c x ≠ c y :=
  Sanity.unit_triangle_no_two_colouring

/-- A single unit edge rules out the one-colour analogue of Theorem 2. -/
theorem edges_le_245510_one_colour_false :
    ¬ ∀ E : Finset (Plane × Plane), (∀ e ∈ E, dist e.1 e.2 = 1) →
      E.card ≤ 245510 → ∃ c : Plane → Fin 1, ∀ e ∈ E, c e.1 ≠ c e.2 :=
  Sanity.edges_le_245510_one_colour_false

/-- Two points at distance one rule out the one-colour analogue of Theorem 1. -/
theorem points_le_10689_one_colour_false :
    ¬ ∀ X : Finset Plane, X.card ≤ 10689 → ∃ c : Plane → Fin 1,
      ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → c x ≠ c y :=
  Sanity.points_le_10689_one_colour_false

end HadwigerNelson
