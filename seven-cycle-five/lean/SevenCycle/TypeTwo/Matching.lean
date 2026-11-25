import SevenCycle.Blueprint.Definitions

/-! ## Matching constraints for type-two layouts -/

namespace SevenCycle.TypeTwo

open Blueprint.SearchSpec
open SevenCycle.Proof

abbrev Edge := Tuple 4 × Tuple 4

theorem filtered_image_card {α β : Type*} [DecidableEq β] (f : α → β)
    (D : Finset α) (S X : Finset β) (hi : Set.InjOn f D) (him : D.image f = S)
    (hX : X ⊆ S) : (D.filter fun a => f a ∈ X).card = X.card := by
  have him' : (D.filter fun a => f a ∈ X).image f = X := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (him ▸ hX hx : x ∈ D.image f)
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
  exact (Finset.card_image_of_injOn (hi.mono (Finset.filter_subset _ _))).symm.trans
    (congrArg Finset.card him')

theorem endpoint_images {S T : Points} {M : Finset Edge} (hM : Perfect S T M) :
    (M.image Prod.fst = S ∧ Set.InjOn Prod.fst (M : Set Edge)) ∧
    (M.image Prod.snd = T ∧ Set.InjOn Prod.snd (M : Set Edge)) := by
  obtain ⟨mem, left, right⟩ := hM
  constructor
  · constructor
    · ext x
      constructor
      · rintro hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
        exact (mem e he).1
      · intro hx
        obtain ⟨y, he, _⟩ := left x hx
        exact Finset.mem_image.mpr ⟨(x,y), he, rfl⟩
    · rintro ⟨x,y⟩ h ⟨x',z⟩ h' heq
      change x = x' at heq
      subst x'
      exact Prod.ext rfl ((left x (mem _ h).1).unique h h')
  · constructor
    · ext y
      constructor
      · intro hy
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
        exact (mem e he).2.1
      · intro hy
        obtain ⟨x, he, _⟩ := right y hy
        exact Finset.mem_image.mpr ⟨(x,y), he, rfl⟩
    · rintro ⟨x,y⟩ h ⟨z,y'⟩ h' heq
      change y = y' at heq
      subst y'
      exact Prod.ext ((right y (mem _ h).2.1).unique h h') rfl

/-- For every perfect matching, a middle-level assignment occupies distinct edges.
At most two edges are empty when the middle band contains at least 31 words. -/
theorem matching_bounds {S T X Y : Points} {M : Finset Edge} (hM : Perfect S T M)
    (hX : X ⊆ S) (hY : Y ⊆ T) (hdisj : Disjoint X Y)
    (hpack : packing cycleStep (X ∪ Y)) (hsize : S.card = 33)
    (hmiddle : 31 ≤ X.card + Y.card) :
    (∀ e ∈ M, ¬ (e.1 ∈ X ∧ e.2 ∈ Y)) ∧
    (M.filter fun e => e.1 ∉ X ∧ e.2 ∉ Y).card ≤ 2 := by
  have hboth : ∀ e ∈ M, ¬ (e.1 ∈ X ∧ e.2 ∈ Y) := by
    rintro ⟨x,y⟩ he ⟨hx, hy⟩
    have edge : x = y ∨ conflict cycleStep x y := (hM.1 _ he).2.2
    rcases edge with rfl | h
    · exact Finset.disjoint_left.mp hdisj hx hy
    · exact hpack x (Finset.mem_union_left _ hx) y (Finset.mem_union_right _ hy) h
  refine ⟨hboth, ?_⟩
  obtain ⟨⟨ls, li⟩, ⟨rs, ri⟩⟩ := endpoint_images hM
  have hL := filtered_image_card Prod.fst M S X li ls hX
  have hR := filtered_image_card Prod.snd M T Y ri rs hY
  have hn := Finset.card_image_of_injOn li
  rw [ls, hsize] at hn
  have disj : Disjoint (M.filter fun e => e.1 ∈ X) (M.filter fun e => e.2 ∈ Y) := by
    refine Finset.disjoint_left.mpr fun ⦃e⦄ h₁ h₂ => ?_
    exact hboth e (Finset.mem_filter.mp h₁).1
      ⟨(Finset.mem_filter.mp h₁).2, (Finset.mem_filter.mp h₂).2⟩
  have hu := Finset.card_union_of_disjoint disj
  rw [← Finset.filter_or, hL, hR] at hu
  have n := Finset.card_filter_add_card_filter_not (s := M) (fun e => e.1 ∈ X ∨ e.2 ∈ Y)
  simp only [not_or] at n
  omega

end SevenCycle.TypeTwo
