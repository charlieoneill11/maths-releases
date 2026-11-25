import SevenCycleRuntime.Middle
import SevenCycle.Adjacent.Support
import SevenCycle.Blueprint.Definitions

namespace SevenCycle.Adjacent.Middle

open Proof Bitsets Blueprint

def Site.word (v : Site) : Tuple 3 := ![v.x,v.y,v.z]

def Site.ofWord (w : Tuple 3) : Site := ⟨w 0, w 1, w 2⟩

@[simp] theorem Site.word_ofWord (w : Tuple 3) : (Site.ofWord w).word = w := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem Site.ofWord_word (v : Site) : Site.ofWord v.word = v := by cases v; rfl

theorem occupied_iff (u : Cube) (v : Site) : occupied u v = true ↔ v.word ∈ cubeSet u := by
  rw [mem_cubeSet]
  simp [occupied, cubeMem, Site.word]
  rfl

theorem mem_sites (v : Site) (u : Cube) : v ∈ sites u ↔ occupied u v = true := by
  simp only [sites, Array.mem_flatMap, Array.mem_filter, Array.mem_map]
  constructor
  · rintro ⟨_, _, _, _, _, h⟩; exact h
  · intro hv
    refine ⟨v.x, Array.mem_ofFn.mpr ⟨v.x,rfl⟩, v.y, Array.mem_ofFn.mpr ⟨v.y,rfl⟩, ?_, hv⟩
    exact ⟨v.z, Array.mem_ofFn.mpr ⟨v.z, rfl⟩, rfl⟩

private theorem flags_list_bit {α : Type} (p : α → Bool) (xs : List α) (i : Nat) :
    (xs.foldr (fun x n => 2*n+(p x).toNat) 0).testBit i = ((xs[i]?).map p).getD false := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => cases hx : p x <;> simp [hx, Nat.add_mod]
    | succ i =>
      simp only [List.foldr_cons, List.getElem?_cons_succ]
      rw [← Nat.testBit_div_two]
      have half (n : Nat) (b : Bool) : (2*n+b.toNat)/2 = n := by cases b <;> simp; omega
      rw [half, ih]

theorem flags_bit {α : Type} (xs : Array α) (p : α → Bool) (i : Nat) :
    (flags xs p).testBit i = ((xs[i]?).map p).getD false := by
  simpa only [flags, ← Array.foldr_toList, Array.getElem?_toList] using flags_list_bit p xs.toList i

theorem flags_congr {α : Type} {xs : Array α} {p q : α → Bool} (eq : ∀ x ∈ xs, p x = q x) :
    flags xs p = flags xs q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [flags_bit, flags_bit]
  cases h : xs[i]? with
  | none => rfl
  | some x => simp [eq x (Array.mem_of_getElem? h)]

theorem flags_and {α : Type} (xs : Array α) (p q : α → Bool) :
    flags xs p &&& flags xs q = flags xs (fun x => p x && q x) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, flags_bit, flags_bit, flags_bit]
  cases xs[i]? <;> rfl

theorem flags_bound {α : Type} (xs : Array α) (p : α → Bool) : flags xs p < 2^xs.size := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [flags_bit, Array.getElem?_eq_none hi]

private theorem coord (u v : Site) (h : u.x = v.x) :
    7*u.y.val+u.z.val = 7*v.y.val+v.z.val ↔ u = v := by
  constructor
  · intro e
    have uz := u.z.isLt; have vz := v.z.isLt
    have hy : u.y = v.y := Fin.ext (by omega)
    have hz : u.z = v.z := Fin.ext (by omega)
    cases u; cases v; simp_all
  · rintro rfl; rfl

private theorem inserted (u : Cube) (v w : Site) :
    occupied (u.set v.x.val ((u.get v.x) ||| (2^(7*v.y.val+v.z.val) : Nat).toUInt64)) w =
      (occupied u w || decide (v = w)) := by
  change ((u.set v.x.val (u[v.x.val] ||| (2^(7*v.y.val+v.z.val) : Nat).toUInt64))[w.x.val]).toNat.testBit _ = (u[w.x.val].toNat.testBit _ || decide (v = w))
  by_cases h : v.x = w.x
  · have exp : 7*v.y.val+v.z.val < 64 := by have := v.y.isLt; have := v.z.isLt; omega
    have pow : 2^(7*v.y.val+v.z.val) < 2^64 := Nat.pow_lt_pow_right (by decide) exp
    simp only [Vector.getElem_set, congrArg Fin.val h, if_true, UInt64.toNat_or, Nat.testBit_or,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt pow, Nat.testBit_two_pow, coord v w h]
  · have ne : v ≠ w := fun e => h (e ▸ rfl)
    simp only [Vector.getElem_set_ne (h := fun e => h (Fin.ext e)), ne, decide_false,
      Bool.or_false]

theorem materialize_mem (xs : Array Site) (mask : Nat) (v : Site) :
    occupied (materialize xs mask) v = true ↔ ∃ i, xs[i]? = some v ∧ mask.testBit i = true := by
  let insert (u : Cube) (z : Site × Nat) := if mask.testBit z.2 then
    u.set z.1.x.val ((u.get z.1.x) ||| (2^(7*z.1.y.val+z.1.z.val) : Nat).toUInt64) else u
  have go (l : List (Site × Nat)) (u : Cube) :
      occupied (l.foldl insert u) v = true ↔ occupied u v = true ∨ ∃ i, (v,i) ∈ l ∧ mask.testBit i = true := by
    induction l generalizing u with
    | nil => simp
    | cons z l ih =>
      obtain ⟨x,i⟩ := z
      simp only [List.foldl_cons, ih, insert]
      cases hi : mask.testBit i <;>
        simp only [Bool.false_eq_true, if_false, if_true, inserted, Bool.or_eq_true,
          decide_eq_true_eq, List.mem_cons, Prod.mk.injEq] <;> aesop
  change occupied ((xs.zipIdx).foldl insert (Vector.replicate 7 0)) v = true ↔ _
  rw [← Array.foldl_toList, go]
  have empty : occupied (Vector.replicate 7 0) v = false := by simp [occupied, Vector.get]
  simp only [empty, Bool.false_eq_true, false_or, Array.mem_toList_iff]
  simp [Array.mem_zipIdx_iff_getElem?]

/-- Decoding the flags of a genuine subset gives back its exact physical cube set. -/
theorem materialize_correct (s u : Cube) (hs : cubeSet u ⊆ cubeSet s) :
    cubeSet (materialize (sites s) (flags (sites s) (occupied u))) = cubeSet u := by
  ext x
  let v := Site.ofWord x
  have hv : v.word = x := Site.word_ofWord x
  rw [← hv, ← occupied_iff, ← occupied_iff, materialize_mem]
  constructor
  · rintro ⟨i,hi,h⟩
    simpa [flags_bit, hi] using h
  · intro h
    have hm := (mem_sites v s).mpr ((occupied_iff s v).mpr (hs ((occupied_iff u v).mp h)))
    obtain ⟨i,hi,hv⟩ := Array.mem_iff_getElem.mp hm
    have e : (sites s)[i]? = some v := by rw [Array.getElem?_eq_getElem hi, hv]
    exact ⟨i,e,by simp [flags_bit, e, h]⟩

end SevenCycle.Adjacent.Middle
