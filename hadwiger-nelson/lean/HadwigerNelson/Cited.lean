import HadwigerNelson.Plane
import Mathlib.Topology.UnitInterval
import Mathlib.Data.Set.Card

/-! The drawing conventions of §5 of the Hadwiger–Nelson paper. Vertices and
edges have finite labels. Ordering the two endpoints gives a unique orientation
of an undirected edge and still permits parallel edges in the underlying model. -/
namespace HadwigerNelson

/-- A finite labelled loopless multigraph with `n` vertices and `m` edges. -/
structure Graph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  ordered : ∀ e, left e < right e

/-- A simple graph has at most one edge with any given endpoint pair. -/
def Graph.IsSimple {n m : ℕ} (G : Graph n m) : Prop :=
  Function.Injective (fun e => (G.left e, G.right e))

/-- Two edges share an endpoint. -/
def Graph.Incident {n m : ℕ} (G : Graph n m) (e f : Fin m) : Prop :=
  G.left e = G.left f ∨ G.left e = G.right f ∨
  G.right e = G.left f ∨ G.right e = G.right f

/-- Distinct vertex locations and Jordan arcs joining their assigned endpoints.
The open arc of each edge avoids every vertex. -/
structure Drawing {n m : ℕ} (G : Graph n m) where
  vertex : Fin n → Plane
  vertex_injective : Function.Injective vertex
  arc : Fin m → unitInterval → Plane
  arc_continuous : ∀ e, Continuous (arc e)
  arc_injective : ∀ e, Function.Injective (arc e)
  at_zero : ∀ e, arc e 0 = vertex (G.left e)
  at_one : ∀ e, arc e 1 = vertex (G.right e)
  avoids_vertices : ∀ e t, t ≠ 0 → t ≠ 1 → ∀ v, arc e t ≠ vertex v

namespace Drawing
variable {n m : ℕ} {G : Graph n m}

/-- The arc without its two endpoints. -/
def interior (D : Drawing G) (e : Fin m) : Set Plane :=
  D.arc e '' {t | t ≠ 0 ∧ t ≠ 1}

/-- Each pair of distinct edges has finitely many common points, including endpoints. -/
def FiniteIntersections (D : Drawing G) : Prop :=
  ∀ e f, e ≠ f → (Set.range (D.arc e) ∩ Set.range (D.arc f)).Finite

/-- Each pair of distinct edge labels is counted once at each common interior
point. A point shared by three open arcs contributes three to this count. -/
noncomputable def crossingCount (D : Drawing G) : ℕ :=
  Set.ncard {p : Fin m × Fin m × Plane |
    p.1 < p.2.1 ∧ p.2.2 ∈ D.interior p.1 ∧ p.2.2 ∈ D.interior p.2.1}

/-- Crossings on a specified edge, counted once per other edge and point. -/
noncomputable def crossingsOn (D : Drawing G) (e : Fin m) : ℕ :=
  Set.ncard {p : Fin m × Plane |
    p.1 ≠ e ∧ p.2 ∈ D.interior e ∧ p.2 ∈ D.interior p.1}

/-- In local topological coordinates about the crossing the two open arcs are
the two coordinate axes. This permits curved edges and requires a proper crossing. -/
def ProperCrossing (D : Drawing G) (e f : Fin m) (z : Plane) : Prop :=
  ∃ (U V : Set Plane) (_ : IsOpen U) (_ : IsOpen V) (hz : z ∈ U) (h : U ≃ₜ V),
    (h ⟨z, hz⟩ : Plane) = 0 ∧ ∀ x : U,
      ((x : Plane) ∈ D.interior e ↔ (h x : Plane) 1 = 0) ∧
      ((x : Plane) ∈ D.interior f ↔ (h x : Plane) 0 = 0)

/-- A simple topological drawing in general position as in Büngener et al.,
§2. Adjacent edges do not cross, any two edges meet at most once, all interior
meetings are proper crossings, and no three open arcs meet at a point. -/
structure IsGood (D : Drawing G) : Prop where
  adjacent : ∀ e f, e ≠ f → G.Incident e f → Disjoint (D.interior e) (D.interior f)
  at_most_once : ∀ e f, e ≠ f → (Set.range (D.arc e) ∩ Set.range (D.arc f)).Subsingleton
  proper : ∀ e f, e ≠ f → ∀ z ∈ D.interior e ∩ D.interior f, D.ProperCrossing e f z
  no_triple : ∀ e f g, e ≠ f → f ≠ g → e ≠ g →
    ∀ z ∈ D.interior e ∩ D.interior f, z ∉ D.interior g

end Drawing

/-- The ordinary crossing number, minimized over good drawings. The convention
for an empty infimum is immaterial for simple graphs by `CitedFacts.attained`. -/
noncomputable def crossingNumber {n m : ℕ} (G : Graph n m) : ℕ :=
  sInf {k : ℕ | ∃ D : Drawing G, D.IsGood ∧ D.crossingCount = k}

/-- External graph-drawing results used for the point bound. -/
structure CitedFacts : Prop where
  /-- Büngener–Kaufmann, JGAA 29 (2025), Theorem 4(b), equivalently
  arXiv:2409.01733v2, Theorem 6(b). The inequality is multiplied by nine. -/
  crossing_lower : ∀ {n m} (G : Graph n m), G.IsSimple → 3 ≤ n →
    45 * (m : ℤ) - 203 * ((n : ℤ) - 2) ≤ 9 * (crossingNumber G : ℤ)
  /-- Büngener–Franz–Kaufmann–Pfister, GD 2026, Theorem 7.
  A simple 5-planar graph has at most 7(n − 2) edges. -/
  five_planar : ∀ {n m} (G : Graph n m), G.IsSimple → 3 ≤ n →
    ∀ D : Drawing G, D.IsGood → (∀ e, D.crossingsOn e ≤ 5) → m ≤ 7 * (n - 2)
  /-- Schaefer, DS21, “What is a drawing?” and “The crossing number”.
  Perturbing arbitrary drawings into general position gives this comparison
  when each pair of edges has finitely many common points (paper §5). -/
  le_drawing : ∀ {n m} (G : Graph n m), G.IsSimple → ∀ D : Drawing G,
    D.FiniteIntersections → crossingNumber G ≤ D.crossingCount
  /-- Schaefer, DS21, “The crossing number”. A simple graph has a good drawing
  attaining its ordinary crossing number, including graphs with isolated vertices. -/
  attained : ∀ {n m} (G : Graph n m), G.IsSimple →
    ∃ D : Drawing G, D.IsGood ∧ D.crossingCount = crossingNumber G

end HadwigerNelson
