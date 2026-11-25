import HadwigerNelson.Cited
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Set.Finite.Lattice

/-! Restrictions of the signed model of a graph drawing and its finite crossing events. -/
namespace HadwigerNelson.Crossings

open Set

noncomputable section
variable {n m k l : ℕ} {G : Graph n m}

/-- Reindex a subdrawing by increasing embeddings of its vertex and edge labels. -/
structure Selection (G : Graph n m) (k l : ℕ) where
  vertex : Fin k ↪o Fin n
  edge : Fin l ↪o Fin m
  left : Fin l → Fin k
  right : Fin l → Fin k
  map_left : ∀ e, vertex (left e) = G.left (edge e)
  map_right : ∀ e, vertex (right e) = G.right (edge e)

namespace Selection

def graph (s : Selection G k l) : Graph k l where
  left := s.left
  right := s.right
  ordered e := s.vertex.lt_iff_lt.mp (by rw [s.map_left, s.map_right]; exact G.ordered _)

theorem simple (s : Selection G k l) (hg : G.IsSimple) : s.graph.IsSimple := by
  intro e f h
  apply s.edge.injective
  apply hg
  apply Prod.ext
  · simpa only [← s.map_left] using congrArg s.vertex (congrArg Prod.fst h)
  · simpa only [← s.map_right] using congrArg s.vertex (congrArg Prod.snd h)

def drawing (s : Selection G k l) (D : Drawing G) : Drawing s.graph where
  vertex := D.vertex ∘ s.vertex
  vertex_injective := D.vertex_injective.comp s.vertex.injective
  arc e := D.arc (s.edge e)
  arc_continuous e := D.arc_continuous (s.edge e)
  arc_injective e := D.arc_injective (s.edge e)
  at_zero e := (D.at_zero _).trans (congrArg D.vertex (s.map_left e).symm)
  at_one e := (D.at_one _).trans (congrArg D.vertex (s.map_right e).symm)
  avoids_vertices e t h0 h1 v := D.avoids_vertices (s.edge e) t h0 h1 (s.vertex v)

theorem finite (s : Selection G k l) (D : Drawing G) (hD : D.FiniteIntersections) :
    (s.drawing D).FiniteIntersections := fun _ _ h ↦ hD _ _ (s.edge.injective.ne h)

@[simp] theorem interior (s : Selection G k l) (D : Drawing G) (e : Fin l) :
    (s.drawing D).interior e = D.interior (s.edge e) := rfl

/-- Choose any subset of edge labels while keeping the full vertex set. -/
def spanning (G : Graph n m) (S : Finset (Fin m)) : Selection G n S.card where
  vertex := (OrderIso.refl _).toOrderEmbedding
  edge := S.orderEmbOfFin rfl
  left i := G.left (S.orderEmbOfFin rfl i)
  right i := G.right (S.orderEmbOfFin rfl i)
  map_left _ := rfl
  map_right _ := rfl

end Selection

theorem good_finite {D : Drawing G} (h : D.IsGood) : D.FiniteIntersections :=
  fun e f hef ↦ (h.at_most_once e f hef).finite

def eventSet (D : Drawing G) : Set (Fin m × Fin m × Plane) :=
  {p | p.1 < p.2.1 ∧ p.2.2 ∈ D.interior p.1 ∧ p.2.2 ∈ D.interior p.2.1}

def onSet (D : Drawing G) (e : Fin m) : Set (Fin m × Plane) :=
  {p | p.1 ≠ e ∧ p.2 ∈ D.interior e ∧ p.2 ∈ D.interior p.1}

def Crossing (D : Drawing G) := ↥(eventSet D)
def On (D : Drawing G) (e : Fin m) := ↥(onSet D e)

theorem finite_events (D : Drawing G) (h : D.FiniteIntersections) : (eventSet D).Finite := by
  let points (e f : Fin m) : Set Plane := if e = f then ∅ else Set.range (D.arc e) ∩ Set.range (D.arc f)
  have hp (e f : Fin m) : (points e f).Finite := by
    by_cases he : e = f <;> simp only [points, he, if_true, if_false]
    · exact finite_empty
    · exact h e f he
  apply (Set.finite_iUnion (fun e : Fin m ↦ Set.finite_iUnion
    (fun f : Fin m ↦ (hp e f).image (fun z ↦ (e,f,z))))).subset
  rintro ⟨e,f,z⟩ ⟨hef,he,hf⟩
  refine Set.mem_iUnion_of_mem e (Set.mem_iUnion_of_mem f ?_)
  refine ⟨z, ?_, rfl⟩
  change z ∈ (if e = f then ∅ else Set.range (D.arc e) ∩ Set.range (D.arc f))
  rw [if_neg (show e ≠ f from hef.ne)]
  exact ⟨Set.image_subset_range _ _ he,Set.image_subset_range _ _ hf⟩

theorem card_crossing (D : Drawing G) : Nat.card (Crossing D) = D.crossingCount := rfl
theorem card_on (D : Drawing G) (e : Fin m) : Nat.card (On D e) = D.crossingsOn e := rfl

end
end HadwigerNelson.Crossings
