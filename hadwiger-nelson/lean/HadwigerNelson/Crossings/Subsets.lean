import HadwigerNelson.Crossings.Deletion
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Powerset

namespace HadwigerNelson.Crossings

open Set Finset
noncomputable section
variable {n m k l : ℕ} {G : Graph n m}

def events (D : Drawing G) (h : D.FiniteIntersections) : Finset (Fin m × Fin m × Plane) :=
  (finite_events D h).toFinset

@[simp] theorem mem_events (D : Drawing G) (h : D.FiniteIntersections) (p : Fin m × Fin m × Plane) :
    p ∈ events D h ↔ p ∈ eventSet D := (finite_events D h).mem_toFinset

@[simp] theorem card_events (D : Drawing G) (h : D.FiniteIntersections) :
    (events D h).card = D.crossingCount := (Set.ncard_eq_toFinset_card _ _).symm

/-- Compare crossing events of a subdrawing to all original events whose two edges survive. -/
theorem Selection.count_le_filter (s : Selection G k l) (D : Drawing G) (h : D.FiniteIntersections)
    (keep : Fin m → Prop) [DecidablePred keep] (hs : ∀ e, keep (s.edge e)) :
    (s.drawing D).crossingCount ≤
      ((events D h).filter fun p ↦ keep p.1 ∧ keep p.2.1).card := by
  let T := (events D h).filter fun p ↦ keep p.1 ∧ keep p.2.1
  let f : Crossing (s.drawing D) → T := fun p ↦ ⟨(s.eventMap D p).val,
    Finset.mem_filter.mpr ⟨(mem_events _ _ _).mpr (s.eventMap D p).property,hs _,hs _⟩⟩
  have inj : Function.Injective f := by
    intro p q he
    exact s.eventMap_injective D (Subtype.ext (congrArg (fun t : T ↦ t.val) he))
  have bound := Nat.card_le_card_of_injective f inj
  simpa only [T,card_crossing,Nat.card_eq_finsetCard] using bound

theorem sum_filter_card {α β : Type*} (A : Finset α) (B : Finset β)
    (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
    (∑ a ∈ A, (B.filter (p a)).card) = ∑ b ∈ B, (A.filter fun a ↦ p a b).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

def ends (G : Graph n m) (e : Fin m) : Finset (Fin n) := {G.left e,G.right e}

@[simp] theorem card_ends (G : Graph n m) (e : Fin m) : (ends G e).card = 2 := by
  simp [ends,(G.ordered e).ne]

theorem four_ends (D : Drawing G) (hD : D.IsGood) (p : Fin m × Fin m × Plane) (hp : p ∈ eventSet D) :
    (ends G p.1 ∪ ends G p.2.1).card = 4 := by
  obtain ⟨hef,he,hf⟩ := hp
  have different : ¬G.Incident p.1 p.2.1 := fun h ↦ Set.disjoint_left.mp (hD.adjacent _ _ hef.ne h) he hf
  unfold Graph.Incident at different
  have dis : Disjoint (ends G p.1) (ends G p.2.1) := by
    apply Finset.disjoint_left.mpr
    intro v a b
    simp only [ends,Finset.mem_insert,Finset.mem_singleton] at a b
    rcases a with rfl | rfl <;> rcases b with b|b <;> tauto
  rw [Finset.card_union_of_disjoint dis, card_ends, card_ends]

def keptEdges (G : Graph n m) (V : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun e ↦ ends G e ⊆ V

def induced (G : Graph n m) (V : Finset (Fin n)) {k : ℕ} (hk : V.card = k) :
    Selection G k (keptEdges G V).card := by
  let E := keptEdges G V
  let idx := E.orderEmbOfFin rfl
  have hv (i : Fin E.card) : ends G (idx i) ⊆ V :=
    (Finset.mem_filter.mp (E.orderEmbOfFin_mem rfl i)).2
  let L (i : Fin E.card) : ↥V := ⟨G.left (idx i),hv i (by simp [ends])⟩
  let R (i : Fin E.card) : ↥V := ⟨G.right (idx i),hv i (by simp [ends])⟩
  let mapv := V.orderIsoOfFin hk
  refine ⟨V.orderEmbOfFin hk, idx, fun i ↦ mapv.symm (L i), fun i ↦ mapv.symm (R i), ?_, ?_⟩
  · intro i; exact congrArg Subtype.val (mapv.apply_symm_apply (L i))
  · intro i; exact congrArg Subtype.val (mapv.apply_symm_apply (R i))

theorem induced_keeps (G : Graph n m) (V : Finset (Fin n)) {k : ℕ} (hk : V.card = k)
    (e : Fin (keptEdges G V).card) : ends G ((induced G V hk).edge e) ⊆ V :=
  (Finset.mem_filter.mp ((keptEdges G V).orderEmbOfFin_mem rfl e)).2

end
end HadwigerNelson.Crossings
