import SevenCycle.Adjacent.Frames
import SevenCycle.Adjacent.UnionMasks

namespace SevenCycle.Adjacent.SlabJoin

open Proof Blueprint

/-- The contents of one supplied slab row, using the base-seven site labels. -/
def rowPoints (row : String) : Finset (Tuple 4) :=
  ((readSlab row).toList.filter (· < 2401)).toFinset.image position

def signedAction (p : AxisOrder) (s : Nat) (x : Tuple 4) : Tuple 4 :=
  fun k => if s.testBit k.val then -x p[k] else x p[k]

theorem orders_complete (p : AxisOrder) (h : Function.Injective (fun k : Fin 4 => p[k])) :
    p ∈ orders := by
  have all : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (#v[a,b,c,d] : AxisOrder) ∈ orders := by decide +kernel
  have dist (i j : Fin 4) (n : i ≠ j) : p[i] ≠ p[j] := fun e => n (h e)
  have rep : (#v[p[0], p[1], p[2], p[3]] : AxisOrder) = p := by
    ext i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  exact rep ▸ all p[0] p[1] p[2] p[3] (dist 0 1 (by decide)) (dist 0 2 (by decide))
    (dist 0 3 (by decide)) (dist 1 2 (by decide)) (dist 1 3 (by decide)) (dist 2 3 (by decide))

theorem transforms_complete {k : Fin 4} (p : AxisOrder) (s : Fin 16)
    (hi : Function.Injective (fun j : Fin 4 => p[j])) (hn : p[k] = 0)
    (first : k = 0 → p = identityOrder ∧ s.val = 0) : (p,s.val) ∈ transforms k := by
  by_cases hk : k = 0
  · obtain ⟨rfl,hs⟩ := first hk
    simp [transforms, hk, hs]
  · simp only [transforms,hk,if_false,Array.mem_flatMap,Array.mem_filter,Array.mem_map]
    exact ⟨p,⟨orders_complete p hi, by simp [hn]⟩,s.val, by simp [s.isLt],rfl⟩

private theorem transform_address (p : AxisOrder) (s : Nat) (i : Fin 2401) :
    transformedSite p s i.val = address (signedAction p s (position i.val)) := by
  have value (k : Fin 4) : (if s.testBit k.val then (7 - coords i.val p[k]) % 7 else coords i.val p[k]) =
      ((signedAction p s (position i.val)) k).val := by
    rw [coords_position i p[k]]
    unfold signedAction
    split <;> simp [ZMod.neg_val']
  simp only [transformedSite,address,value]

private theorem wordFold (xs : List Nat) (m : Array Nat) (start j : Nat) :
    (xs.foldl (fun acc i => acc ||| (m[i]?.getD 0)) start).testBit j = true ↔
      start.testBit j = true ∨ ∃ i ∈ xs, (m[i]?.getD 0).testBit j = true := by
  induction xs generalizing start with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true_iff,List.mem_cons]
    aesop

theorem addressMap_stores (r : String) (f : Tuple 4 → Tuple 4) (m : Array Nat)
    (sz : m.size = 2401) (mapped : ∀ (i : Nat), i < 2401 → m[i]? = some (1 <<< address (f (position i)))) :
    Stores (movedMask m (readSlab r)) ((rowPoints r).image f) := by
  intro j
  rw [movedMask,← Array.foldl_toList,wordFold]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,Array.mem_toList_iff]
  constructor
  · rintro ⟨i,hr,hit⟩
    by_cases hi : i < 2401
    · rw [mapped i hi] at hit
      simp only [Option.getD_some,Nat.one_shiftLeft,Nat.testBit_two_pow,decide_eq_true_eq] at hit
      rw [← hit]
      obtain ⟨lt,eq⟩ := UnionMasks.components (f (position i))
      rw [eq]
      refine ⟨lt,Finset.mem_image.mpr ⟨position i,?_,rfl⟩⟩
      exact Finset.mem_image.mpr ⟨i,by simp [hr,hi],rfl⟩
    · have size : m.size ≤ i := by simpa [sz] using Nat.le_of_not_lt hi
      rw [Array.getElem?_eq_none size] at hit
      simp at hit
  · rintro ⟨hj,mem⟩
    obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp mem
    obtain ⟨i,hin,rfl⟩ := Finset.mem_image.mp hx
    simp only [List.mem_toFinset,List.mem_filter,Array.mem_toList_iff,decide_eq_true_eq] at hin
    refine ⟨i,hin.1,?_⟩
    rw [mapped i hin.2]
    simp only [Option.getD_some,Nat.one_shiftLeft,Nat.testBit_two_pow,decide_eq_true_eq]
    exact (congrArg address eq).trans (address_position ⟨j,hj⟩)

theorem moved_stores (r : String) (p : AxisOrder) (s : Nat) :
    Stores (movedMask (oneBitMap p s) (readSlab r)) ((rowPoints r).image (signedAction p s)) := by
  apply addressMap_stores r _ _ (by simp [oneBitMap])
  intro i hi
  simp [oneBitMap,hi,transform_address p s ⟨i,hi⟩]

/-- A geometric source row supplies the coverage hypothesis for the joined search. -/
theorem comesFrom_image {rows : Array String} {k : Fin 4} {r : String} (hr : r ∈ rows)
    (p : AxisOrder) (s : Fin 16) (hi : Function.Injective (fun j : Fin 4 => p[j]))
    (hn : p[k] = 0) (first : k = 0 → p = identityOrder ∧ s.val = 0) :
    ComesFrom rows k ((rowPoints r).image (signedAction p s)) :=
  ⟨r, hr, (p,s.val), transforms_complete p s hi hn first, moved_stores r p s.val⟩

end SevenCycle.Adjacent.SlabJoin
