import HadwigerNelson.Stars.OneBadEdge
import Mathlib.Data.Finset.Max

/-! Component counting for a finite rooted forest. Each nonroot contributes
one edge to its parent, so the blank–blank edges are counted by their children. -/

namespace HadwigerNelson.Stars

variable {V : Type*}

/-- The orientation toward the root of each forest component. A topological
ordering, for instance the distance to the root, witnesses the rank decrease. -/
structure RootedForest (V : Type*) where
  parent : V → Option V
  rank : V → ℕ
  decreases : ∀ v p, parent v = some p → rank p < rank v

namespace RootedForest

noncomputable def internal (F : RootedForest V) (B : Finset V) : Finset V := by
  classical exact B.filter (fun v => ∃ p ∈ B, F.parent v = some p)

/-- Every nonempty induced subforest has a vertex whose parent is absent. -/
theorem card_internal_lt (F : RootedForest V) {B : Finset V} (hB : B.Nonempty) :
    (F.internal B).card < B.card := by
  classical
  obtain ⟨v,hv,least⟩ := Finset.exists_min_image B F.rank hB
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (Finset.filter_subset ..) |>.mpr ⟨v,hv,?_⟩
  intro hi
  obtain ⟨p,hp,hvp⟩ := (Finset.mem_filter.mp hi).2
  exact (not_lt_of_ge (least p hp)) (F.decreases v p hvp)

/-- The forest supplies exactly the component term of Lemma 20, as the
number of blank vertices minus the number of edges with two blank ends. -/
theorem one_bad_edge_forest (F : RootedForest V) (S : Finset V) (E : Finset (V × V))
    (κ : V → Option (Fin 6))
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (impossible : ¬ ∃ c : V → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2) :
    let B := S.filter (fun v => κ v = none)
    4 ≤ 4 * (B.card - (F.internal B).card) + 2 * badCount E κ + ∑ v ∈ S, locked E κ v := by
  classical
  intro B
  apply one_bad_edge S E κ _ ends loops _ impossible
  rintro ⟨v,hv,hκ⟩
  have mem : v ∈ B := Finset.mem_filter.mpr ⟨hv,hκ⟩
  have := F.card_internal_lt ⟨v,mem⟩
  omega

end RootedForest
end HadwigerNelson.Stars
