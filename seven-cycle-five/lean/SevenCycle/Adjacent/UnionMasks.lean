import SevenCycle.Adjacent.SlabJoin
import SevenCycle.Adjacent.UnionTable

namespace SevenCycle.Adjacent.UnionMasks

open Proof SlabJoin

private def insertWord (bits : ℕ) (w : Tuple 4) : ℕ :=
  bits ||| (1 <<< address w)

def pack (a : Array (Tuple 4)) : ℕ := a.foldl insertWord 0

private theorem fold_bits (xs : List (Tuple 4)) (v j : ℕ) :
    (xs.foldl insertWord v).testBit j = true ↔
    v.testBit j = true ∨ ∃ x ∈ xs, address x = j := by
  induction xs generalizing v with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, insertWord, Nat.testBit_or, Nat.one_shiftLeft,
      Nat.testBit_two_pow, Bool.or_eq_true_iff, decide_eq_true_eq, List.mem_cons]
    aesop

theorem components (x : Tuple 4) : address x < 2401 ∧ position (address x) = x := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  have h3 := ZMod.val_lt (x 3)
  constructor
  · unfold address
    omega
  · have digits : address x / 343 = (x 0).val ∧ address x / 49 % 7 = (x 1).val ∧
        address x / 7 % 7 = (x 2).val ∧ address x % 7 = (x 3).val := by
      unfold address
      omega
    funext k
    fin_cases k
    · change (↑(address x / 343) : ZMod 7) = x 0
      rw [digits.1, ZMod.natCast_zmod_val]
    · change (↑(address x / 49 % 7) : ZMod 7) = x 1
      rw [digits.2.1, ZMod.natCast_zmod_val]
    · change (↑(address x / 7 % 7) : ZMod 7) = x 2
      rw [digits.2.2.1, ZMod.natCast_zmod_val]
    · change (↑(address x % 7) : ZMod 7) = x 3
      rw [digits.2.2.2, ZMod.natCast_zmod_val]

theorem pack_stores (a : Array (Tuple 4)) : Stores (pack a) (rowSet a) := by
  intro j
  rw [pack, ← Array.foldl_toList, fold_bits]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, Array.mem_toList_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k,hk,rfl⟩ := Array.mem_iff_getElem.mp hx
    exact ⟨(components _).1, Finset.mem_image.mpr ⟨⟨k,hk⟩, Finset.mem_univ _, (components _).2.symm⟩⟩
  · rintro ⟨hj, h⟩
    obtain ⟨k, _, eq⟩ := Finset.mem_image.mp h
    exact ⟨a[k], Array.getElem_mem _, (congrArg address eq).trans (address_position ⟨j,hj⟩)⟩

private def masks (rows : Array String) : Std.HashSet ℕ :=
  Std.HashSet.ofArray (rows.map fun s => pack (UnionTable.decode s).inside)

private theorem masks_sound (rows : Array String) (b : ℕ) (h : (masks rows).contains b = true) :
    ∃ s ∈ rows, Stores b (rowSet (UnionTable.decode s).inside) := by
  simp only [masks, Std.HashSet.ofArray_eq_ofList, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Array.mem_toList_iff, Array.mem_map] at h
  obtain ⟨s,hs,rfl⟩ := h
  exact ⟨s,hs,pack_stores _⟩

def knownUnionMasks : Std.HashSet ℕ := masks UnionData.rows

theorem knownUnionMasks_sound (b : ℕ) (h : knownUnionMasks.contains b = true) :
    ∃ s ∈ UnionData.rows, Stores b (rowSet (UnionTable.decode s).inside) :=
  masks_sound _ _ h

end SevenCycle.Adjacent.UnionMasks
