import HadwigerNelson.Crossings.UnitDegrees
import HadwigerNelson.Crossings.CircleIntersections

namespace HadwigerNelson.Crossings

/-- The circle drawing of Lemma 29 before counting crossings. The assigned
center identifies the unit circle supporting each edge. -/
structure UnitArcDrawing (X : Finset Plane) where
  G : Graph X.card (2*unitEdgeCount X)
  D : Drawing G
  center : Fin (2*unitEdgeCount X) → ↥X
  vertex_set : Set.range D.vertex = (X : Set Plane)
  on_circle : ∀ e z, z ∈ Set.range (D.arc e) → dist z (center e : Plane) = 1
  same_center_disjoint : ∀ {e f}, e ≠ f → center e = center f → Disjoint (D.interior e) (D.interior f)
  same_center_endpoint_inj : ∀ {e f}, center e = center f → G.left e = G.left f →
    G.right e = G.right f → e = f

end HadwigerNelson.Crossings
