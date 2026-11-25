import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

namespace HadwigerNelson.Point

/-- A colouring is defined on the ambient type, with constraints on the given finite set. -/
def Colourable {α : Type*} (adj : α → α → Prop) (X : Finset α) : Prop :=
  ∃ c : α → Fin 6, ∀ x ∈ X, ∀ y ∈ X, adj x y → c x ≠ c y

/-- Every finite graph requiring seven or more colours contains an induced
subgraph with minimum degree six which still requires seven or more colours. -/
theorem critical_subset {α : Type*} (adj : α → α → Prop) [DecidableRel adj]
    (sym : Symmetric adj) (loopless : ∀ x, ¬ adj x x)
    (X : Finset α) (bad : ¬ Colourable adj X) :
    ∃ Y ⊆ X, ¬ Colourable adj Y ∧ ∀ x ∈ Y, 6 ≤ (Y.filter (adj x)).card := by
  classical
  let pool := X.powerset.filter fun Y => ¬ Colourable adj Y
  have hpool : X ∈ pool := by simp [pool, bad]
  obtain ⟨Y,hY,hmin⟩ := pool.exists_min_image Finset.card ⟨X,hpool⟩
  obtain ⟨hYX,hbad⟩ : Y ⊆ X ∧ ¬ Colourable adj Y := by simpa [pool] using hY
  refine ⟨Y,hYX,hbad,?_⟩
  intro x hx
  by_contra! small
  have colour_erase : Colourable adj (Y.erase x) := by
    by_contra contra
    have hmem : Y.erase x ∈ pool := by
      simp [pool, (Finset.erase_subset x Y).trans hYX, contra]
    have hcard := hmin _ hmem
    exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hx)) hcard
  obtain ⟨c,hc⟩ := colour_erase
  let N := Y.filter (adj x)
  let palette := N.image c
  have hp : palette.card < (Finset.univ : Finset (Fin 6)).card := by
    simpa [palette] using (Finset.card_image_le.trans_lt small)
  obtain ⟨a,_,fresh⟩ := Finset.exists_mem_notMem_of_card_lt_card hp
  have diff {y} (hy : y ∈ Y) (h : adj x y) : a ≠ c y := by
    intro eq
    exact fresh (eq ▸ Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hy,h⟩))
  apply hbad
  refine ⟨fun y => if y = x then a else c y, ?_⟩
  intro u hu v hv huv
  by_cases hux : u = x <;> by_cases hvx : v = x
  · subst u
    subst v
    exact (loopless x huv).elim
  · subst u
    simpa [hvx] using diff hv huv
  · subst v
    simpa [hux] using (diff hu (sym huv)).symm
  · simpa [hux,hvx] using hc u (Finset.mem_erase.mpr ⟨hux,hu⟩) v
      (Finset.mem_erase.mpr ⟨hvx,hv⟩) huv

/-- In a finite set, choose a maximal pairwise-separated subset. Every omitted
point has a conflict with a member of the chosen subset. -/
theorem maximal_layer {α : Type*} (X : Finset α) (apart : α → α → Prop) (sym : Symmetric apart) :
    ∃ P ⊆ X, (∀ x ∈ P, ∀ y ∈ P, x ≠ y → apart x y) ∧
      ∀ x ∈ X, x ∉ P → ∃ y ∈ P, ¬ apart x y := by
  classical
  let ok (P : Finset α) := ∀ x ∈ P, ∀ y ∈ P, x ≠ y → apart x y
  let pool := X.powerset.filter ok
  have empty : (∅ : Finset α) ∈ pool := by simp [pool,ok]
  obtain ⟨P,hP,hmax⟩ := pool.exists_max_image Finset.card ⟨∅,empty⟩
  obtain ⟨sub,sep⟩ : P ⊆ X ∧ ok P := by simpa [pool] using hP
  refine ⟨P, sub, sep, ?_⟩
  intro x hx hxP
  by_contra! free
  have add : ok (insert x P) := by
    intro u hu v hv huv
    by_cases ux : u = x
    · subst u
      exact free _ ((Finset.mem_insert.mp hv).resolve_left huv.symm)
    · have up := (Finset.mem_insert.mp hu).resolve_left ux
      by_cases vx : v = x
      · subst v
        exact sym (free _ up)
      · exact sep _ up _ ((Finset.mem_insert.mp hv).resolve_left vx) huv
  have add_mem : insert x P ∈ pool :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx sub),add⟩
  have contra := hmax _ add_mem
  rw [Finset.card_insert_of_notMem hxP] at contra
  omega

end HadwigerNelson.Point
