import Mathlib.Data.Finset.Card

/-!
# Exhaustive fixed-size independent set search

A successful call certifies that every pairwise compatible completion visits
a successful leaf. The value checked at a leaf is supplied by the caller.
-/

namespace SevenCycle.Atlas

/-- Enumerate fixed-size extensions. Excluding the pivot removes just the
pivot. Including it also removes every incompatible remaining vertex. -/
def allExtensions {α : Type*} (compatible : α → α → Bool) (leaf : Array α → Bool)
    (fuel need : Nat) (available selected : Array α) : Bool :=
  match need with
  | 0 => leaf selected
  | k+1 =>
    if k+1 > available.size then true
    else
      match fuel with
      | 0 => false
      | f+1 =>
        if h : 0 < available.size then
          let x := available.back
          allExtensions compatible leaf f k (available.pop.filter (compatible x)) (selected.push x) &&
          allExtensions compatible leaf f (k+1) available.pop selected
        else false
termination_by fuel

/-- The array's mathematical support. -/
def support {α : Type*} [DecidableEq α] (a : Array α) : Finset α := a.toList.toFinset

@[simp] theorem mem_support {α : Type*} [DecidableEq α] {x : α} {a : Array α} :
    x ∈ support a ↔ x ∈ a := by simp [support]

@[simp] theorem support_push {α : Type*} [DecidableEq α] (a : Array α) (x : α) :
    support (a.push x) = insert x (support a) := by
  ext y
  simp [Array.mem_push, or_comm]

/-- Given any compatible set of the requested size in the available array,
the successful traversal supplies a checked leaf with exactly those additions. -/
theorem allExtensions_sound {α : Type*} [DecidableEq α] (compatible : α → α → Bool)
    (leaf : Array α → Bool) (fuel need : Nat) (available selected : Array α)
    (D : Finset α) (sizeD : D.card = need)
    (sub : ∀ x ∈ D, x ∈ available)
    (pair : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → compatible x y)
    (h : allExtensions compatible leaf fuel need available selected = true) :
    ∃ a, leaf a = true ∧ support a = support selected ∪ D := by
  induction fuel generalizing available selected need D with
  | zero =>
    cases need with
    | zero =>
      have hD := Finset.card_eq_zero.mp sizeD
      exact ⟨selected, by simpa [allExtensions] using h, by simp [hD]⟩
    | succ k =>
      have hle : k+1 ≤ available.size := by
        rw [← sizeD]
        exact (Finset.card_le_card (fun x hx => mem_support.mpr (sub x hx))).trans
          (by simpa [support] using List.toFinset_card_le available.toList)
      simp [allExtensions, Nat.not_lt.mpr hle] at h
  | succ f ih =>
    cases need with
    | zero =>
      have hD := Finset.card_eq_zero.mp sizeD
      exact ⟨selected, by simpa [allExtensions] using h, by simp [hD]⟩
    | succ k =>
      have hle : k+1 ≤ available.size := by
        rw [← sizeD]
        exact (Finset.card_le_card (fun x hx => mem_support.mpr (sub x hx))).trans
          (by simpa [support] using List.toFinset_card_le available.toList)
      obtain ⟨avail, x, rfl⟩ := Array.exists_push_of_size_pos (by omega : 0 < available.size)
      have hback : (avail.push x).back = x := by simp [Array.back_eq_getElem]
      rw [allExtensions, if_neg (Nat.not_lt.mpr hle)] at h
      simp only [Array.size_push, Nat.zero_lt_succ, dite_true, hback, Array.pop_push,
        Bool.and_eq_true] at h
      by_cases hx : x ∈ D
      · let R := D.erase x
        have hr (y : α) (hy : y ∈ R) : y ∈ avail.filter (compatible x) := by
          obtain ⟨hne, hyD⟩ := Finset.mem_erase.mp hy
          exact Array.mem_filter.mpr ⟨(Array.mem_push.mp (sub y hyD)).resolve_right hne,
            pair x hx y hyD hne.symm⟩
        obtain ⟨a, ha, he⟩ := ih k _ (selected.push x) R (by simp [R, Finset.card_erase_of_mem hx, sizeD])
          hr (fun y hy z hz => pair y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz)) h.1
        refine ⟨a, ha, he.trans ?_⟩
        rw [support_push]
        ext z
        simp only [R, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        by_cases hz : z = x <;> simp_all
      · exact ih (k+1) avail selected D sizeD (fun y hy =>
          (Array.mem_push.mp (sub y hy)).resolve_right (fun e => hx (e ▸ hy))) pair h.2

end SevenCycle.Atlas
