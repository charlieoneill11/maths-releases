import SevenCycle.Atlas.Planar
import Std.Data.HashMap.Lemmas

/-! Indexing a full planar window by each of its possible submasks. -/

namespace SevenCycle.Atlas.Completions

open Bitsets

/-- At a set bit extend each earlier subset by that bit, retaining the original subsets. -/
private def subsetsBelow (m : UInt64) : Nat → Array UInt64
  | 0 => #[0]
  | n+1 =>
    let previous := subsetsBelow m n
    if m.toNat.testBit n then
      previous ++ previous.map (fun p => p ||| (2^n : Nat).toUInt64)
    else previous

def submasks (m : UInt64) : Array UInt64 := subsetsBelow m 49

private def truncate (q : UInt64) (n : Nat) : UInt64 := (q.toNat % 2^n).toUInt64

private theorem trunc_bit (q : UInt64) (n j : Nat) :
    (truncate q n).toNat.testBit j = (decide (j < n) && q.toNat.testBit j) := by
  have hlt : q.toNat % 2^n < 2^64 := (Nat.mod_le _ _).trans_lt q.toNat_lt
  change (q.toNat % 2^n % 2^64).testBit j = _
  rw [Nat.mod_eq_of_lt hlt, Nat.testBit_mod_two_pow]

private theorem trunc_succ (q : UInt64) (n : Nat) (hn : n < 64) :
    truncate q (n+1) = if q.toNat.testBit n then truncate q n ||| (2^n : Nat).toUInt64
      else truncate q n := by
  have hp : 2^n < 2^64 := Nat.pow_lt_pow_right (by decide) hn
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  cases hq : q.toNat.testBit n <;>
    simp only [↓reduceIte, Bool.false_eq_true, trunc_bit, UInt64.toNat_or, Nat.testBit_or,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt hp, Nat.testBit_two_pow] <;>
    rcases lt_trichotomy j n with h | rfl | h <;>
      simp_all [Nat.lt_succ_iff, Nat.ne_of_lt, Nat.ne_of_gt, Nat.not_le_of_gt, Nat.le_of_lt]

private theorem truncate_mem (m q : UInt64) (hsub : planeSet q ⊆ planeSet m) (n : Nat)
    (hn : n ≤ 49) : truncate q n ∈ subsetsBelow m n := by
  induction n with
  | zero => simp only [truncate, subsetsBelow, pow_zero, Nat.mod_one]; simp
  | succ n ih =>
    have hprev := ih (by omega)
    have hn' : n < 49 := by omega
    rw [trunc_succ _ _ (by omega)]
    cases hq : q.toNat.testBit n
    · cases hm : m.toNat.testBit n <;> simp [subsetsBelow, hm, hprev]
    · have hm : m.toNat.testBit n := by
        have hi : index (pointAt n) = n := index_pointAt ⟨n, hn'⟩
        have hx : pointAt n ∈ planeSet q := (mem_planeSet _ _).mpr (by simpa [planeMem, hi] using hq)
        simpa [planeMem, hi] using (mem_planeSet _ _).mp (hsub hx)
      simp only [subsetsBelow, hm, ↓reduceIte, Array.mem_append, Array.mem_map]
      exact Or.inr ⟨_, hprev, rfl⟩

theorem submasks_complete (m q : UInt64) (hq : Canonical q) (hsub : planeSet q ⊆ planeSet m) :
    q ∈ submasks m := by
  have bound : q.toNat < 2^49 := Nat.lt_pow_two_of_testBit _ hq
  have heq : truncate q 49 = q := by rw [truncate, Nat.mod_eq_of_lt bound]; simp
  exact heq ▸ truncate_mem m q hsub 49 (by decide)

abbrev Table := Std.HashMap UInt64 (Array UInt64)

private def addMask (m : UInt64) (table : Table) (q : UInt64) : Table :=
  table.insert q ((table.getD q #[]).push m)

private def indexMask (table : Table) (m : UInt64) : Table :=
  (submasks m).foldl (addMask m) table

/-- Keep one entry for each labelled ten-point mask, since stabilizers can
produce the same mask from several isometries. -/
def distinctMasks : Array UInt64 := Planar.maxMasks.foldl
  (fun (acc : Array UInt64) x => if acc.contains x then acc else acc.push x) #[]

/-- Lookup by the chosen first half returns possible full ten-point masks. -/
def fullTable : Table := distinctMasks.foldl indexMask {}

/-- In a union-like accumulator, a property holds after a fold exactly if it
held initially or one of the processed elements added it. -/
private theorem fold_or {α β : Type} (p : β → Prop) (wins : α → Prop) (f : β → α → β)
    (step : ∀ b x, p (f b x) ↔ p b ∨ wins x) (xs : Array α) (b : β) :
    p (xs.foldl f b) ↔ p b ∨ ∃ x ∈ xs, wins x := by
  have go (ys : List α) (b : β) : p (ys.foldl f b) ↔ p b ∨ ∃ x ∈ ys, wins x := by
    induction ys generalizing b with
    | nil => simp
    | cons x ys ih => simp [ih, step, or_assoc]
  simpa using go xs.toList b

theorem mem_distinctMasks (m : UInt64) : m ∈ distinctMasks ↔ m ∈ Planar.maxMasks := by
  let add := fun (acc : Array UInt64) x => if acc.contains x then acc else acc.push x
  have step (acc : Array UInt64) (x : UInt64) : m ∈ add acc x ↔ m ∈ acc ∨ x = m := by
    by_cases h : x ∈ acc
    · simp only [add, Array.contains_iff_mem.mpr h, ↓reduceIte]
      grind
    · simp [add, h, eq_comm]
  have h := fold_or (fun acc : Array UInt64 => m ∈ acc) (· = m) add step Planar.maxMasks #[]
  simpa [distinctMasks, add] using h

private theorem indexMask_mem (table : Table) (m p q : UInt64) :
    p ∈ (indexMask table m).getD q #[] ↔ p ∈ table.getD q #[] ∨ (p = m ∧ q ∈ submasks m) := by
  have hstep (b : Table) (x : UInt64) :
      p ∈ (addMask m b x).getD q #[] ↔ p ∈ b.getD q #[] ∨ (p = m ∧ x = q) := by
    by_cases h : x = q
    · subst x
      simp [addMask]
    · simp [addMask, Std.HashMap.getD_insert, h]
  have h := fold_or (fun b : Table => p ∈ b.getD q #[]) (fun x => p = m ∧ x = q)
    (addMask m) hstep (submasks m) table
  simpa [indexMask, and_comm, and_left_comm, and_assoc] using h

theorem fullTable_covers (m q : UInt64) (hm : m ∈ Planar.maxMasks) (hq : Canonical q)
    (hsub : planeSet q ⊆ planeSet m) : m ∈ fullTable.getD q #[] := by
  apply (fold_or (fun b : Table => m ∈ b.getD q #[]) (fun p => m = p ∧ q ∈ submasks p)
    indexMask (fun b p => indexMask_mem b p m q) distinctMasks {}).mpr
  exact Or.inr ⟨m, (mem_distinctMasks m).mpr hm, rfl, submasks_complete m q hq hsub⟩

theorem fullTable_contains (m q : UInt64) (hm : m ∈ Planar.maxMasks) (hq : Canonical q)
    (hsub : planeSet q ⊆ planeSet m) : fullTable.contains q = true := by
  have h := fullTable_covers m q hm hq hsub
  cases hc : fullTable.contains q with
  | false => simp [Std.HashMap.getD_eq_fallback_of_contains_eq_false hc] at h
  | true => rfl

end SevenCycle.Atlas.Completions
