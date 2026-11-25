import SevenCycle.Blueprint.Definitions
import Mathlib.Combinatorics.Hall.Finite

/-! Hall's theorem applied to the conflict graph between two maximum codes. -/

namespace SevenCycle.Proof.Matching

open SevenCycle.Blueprint

local notation "Code" => packing cycleStep

private theorem conflict_symm {n : ℕ} {x y : Tuple n} (h : conflict cycleStep x y) :
    conflict cycleStep y x := by
  have hs : ∀ a b : ZMod 7, a - b ∈ ({-1, 0, 1} : Finset (ZMod 7)) →
      b - a ∈ ({-1, 0, 1} : Finset (ZMod 7)) := by decide
  exact ⟨h.1.symm, fun i => hs _ _ (h.2 i)⟩

/-- A Hall subset and the opposite vertices outside its neighbourhood form
a code, since they have no conflict edge in either direction. -/
private theorem independent_union {A B : Finset (Tuple 3)} (hA : Code A) (hB : Code B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, ¬conflictEdge x y) : Code (A ∪ B) := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact hA x hx y hy
  · exact fun h => hsep x hx y hy (.inr h)
  · exact fun h => hsep y hy x hx (.inr (conflict_symm h))
  · exact hB x hx y hy

theorem perfect_matching
    (bound : ∀ C : Finset (Tuple 3), Code C → C.card ≤ 33)
    (S T : Finset (Tuple 3)) (hS : Code S) (hT : Code T)
    (s33 : S.card = 33) (t33 : T.card = 33) :
    ∃ e : ↥S ≃ ↥T, ∀ x : ↥S, conflictEdge x.val (e x).val := by
  classical
  let neighbors (x : ↥S) : Finset ↥T := T.attach.filter fun y => conflictEdge x.val y.val
  have hall (A : Finset ↥S) : A.card ≤ (A.biUnion neighbors).card := by
    let N := A.biUnion neighbors
    let U := A.map (Function.Embedding.subtype _)
    let V := (T.attach \ N).map (Function.Embedding.subtype _)
    have hUS : U ⊆ S := by
      intro x hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hx
      exact u.property
    have hVT : V ⊆ T := by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hy
      exact v.property
    have sep : ∀ x ∈ U, ∀ y ∈ V, ¬conflictEdge x y := by
      intro x hx y hy h
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr
        ⟨u, hu, Finset.mem_filter.mpr ⟨T.mem_attach v, h⟩⟩)
    have disj : Disjoint U V := Finset.disjoint_left.mpr fun {x} hx hy =>
      sep _ hx _ hy (.inl rfl)
    have card := bound (U ∪ V) (independent_union
      (fun x hx y hy => hS x (hUS hx) y (hUS hy))
      (fun x hx y hy => hT x (hVT hx) y (hVT hy)) sep)
    rw [Finset.card_union_of_disjoint disj] at card
    simp only [U, V, Finset.card_map] at card
    have eqn := Finset.card_sdiff_add_card_eq_card
      (show N ⊆ T.attach from fun v _ => T.mem_attach v)
    rw [Finset.card_attach, t33] at eqn
    change A.card ≤ N.card
    omega
  obtain ⟨f, hf, he⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hall
  have eqcard : Fintype.card ↥S = Fintype.card ↥T := by simpa using s33.trans t33.symm
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, eqcard⟩),
    fun x => (Finset.mem_filter.mp (he x)).2⟩

theorem matching_count (S T X Y : Finset (Tuple 3)) (hX : X ⊆ S) (hY : Y ⊆ T)
    (hdisj : Disjoint X Y) (hXY : Code (X ∪ Y)) (s33 : S.card = 33)
    (e : ↥S ≃ ↥T) (he : ∀ x : ↥S, conflictEdge x.val (e x).val) :
    (∀ x ∈ X, ∀ y ∈ Y, ¬conflictEdge x y) ∧
      (S.attach.filter fun x => x.val ∉ X ∧ (e x).val ∉ Y).card = 33 - X.card - Y.card := by
  classical
  have sep : ∀ x ∈ X, ∀ y ∈ Y, ¬conflictEdge x y := by
    intro x hx y hy edge
    rcases edge with rfl | h
    · exact Finset.disjoint_left.mp hdisj hx hy
    · exact hXY _ (Finset.mem_union_left _ hx) _ (Finset.mem_union_right _ hy) h
  refine ⟨sep, ?_⟩
  let L := S.attach.filter fun x => x.val ∈ X
  let R := S.attach.filter fun x => (e x).val ∈ Y
  have cardL : L.card = X.card := by
    exact Finset.card_bij (fun u _ => u.val) (fun _ hu => (Finset.mem_filter.mp hu).2)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun x hx => ⟨⟨x, hX hx⟩, Finset.mem_filter.mpr ⟨S.mem_attach _, hx⟩, rfl⟩)
  have cardR : R.card = Y.card := by
    refine Finset.card_bij (fun u _ => (e u).val) (fun _ hu => (Finset.mem_filter.mp hu).2)
      (fun _ _ _ _ h => e.injective (Subtype.ext h)) ?_
    intro y hy
    let t : ↥T := ⟨y, hY hy⟩
    refine ⟨e.symm t, Finset.mem_filter.mpr ⟨S.mem_attach _, ?_⟩, ?_⟩
    · simpa only [e.apply_symm_apply] using hy
    · simp [t]
  have d : Disjoint L R := Finset.disjoint_left.mpr fun {x} hL hR =>
    sep x.val (Finset.mem_filter.mp hL).2 (e x).val (Finset.mem_filter.mp hR).2 (he x)
  have sides : L ∪ R ⊆ S.attach := fun u _ => S.mem_attach u
  have eqn := Finset.card_sdiff_add_card_eq_card sides
  rw [Finset.card_union_of_disjoint d, cardL, cardR, Finset.card_attach, s33] at eqn
  have rest : (S.attach.filter fun x => x.val ∉ X ∧ (e x).val ∉ Y) = S.attach \ (L ∪ R) := by
    ext u
    simp [L, R]
  rw [rest]
  omega

end SevenCycle.Proof.Matching
