import SevenCycle.Adjacent.MarkedScan
import SevenCycle.Adjacent.SlabOrder
import SevenCycle.Adjacent.MixedEnd

namespace SevenCycle.Adjacent.MixedCommon

open Proof Blueprint Blueprint.SearchSpec SlabJoin
open MixedSlabs (Profile)
open SlabTables (Gaps)

private def weight (n : Nat) : Nat := if n = 1 then 4 else if n = 2 then 1 else 0

def tally (m : Frame) : Nat := ∑ j, weight (m.gap j)

private def tailSum (u : Gaps) : Nat :=
  weight (u.get 0).val + weight (u.get 1).val + weight (u.get 2).val

theorem get_gap (f : Frame) (valid : ValidFrame f) (j : Fin 3) :
    ((Scan.gapsOf f).get j).val = f.gap j.succ := by
  change ((Scan.gapsOf f)[j.val]).val = f.gap j.succ
  simp only [Scan.gapsOf,Vector.getElem_ofFn]
  have h := valid j.succ
  exact ZMod.val_natCast_of_lt (by omega : f.gap j.succ < 7)

private theorem tally_eq (m : Frame) (g : Isometry 4) (valid : ValidFrame m)
    (one : (FrameAction.moved g m).gap 0 = 1) :
    tally m = 4 + tailSum (Scan.gapsOf (FrameAction.moved g m)) := by
  let f := FrameAction.moved g m
  have move : tally m = tally f := (Fintype.sum_equiv g.1 (fun j => weight (f.gap j))
    (fun k => weight (m.gap k)) (fun _ => rfl)).symm
  have vf : ValidFrame f := fun j => valid _
  rw [move]
  change (∑ i : Fin 4, weight (f.gap i)) = 4 + tailSum (Scan.gapsOf f)
  rw [Fin.sum_univ_succ]
  change f.gap 0 = 1 at one
  rw [one]
  simp only [tailSum, get_gap f vf, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change 4 + (weight (f.gap 1) + (weight (f.gap 2) + weight (f.gap 3))) =
    4 + ((weight (f.gap 1) + weight (f.gap 2)) + weight (f.gap 3))
  simp [Nat.add_assoc]

def profileFor (n : Nat) : Profile :=
  if n = 16 then #v[1,1,1,1] else if n = 13 then #v[1,1,1,2]
  else if n = 10 then MixedEnd.twoProfile false else MixedEnd.twoProfile true

def rowsFor (n : Nat) : Array String :=
  if n = 16 then SlabData.rows else if n = 13 then MixedSlabData.rows1112
  else if n = 10 then MixedSlabData.rows1122 else if n = 9 then MixedSlabData.rows1123 else #[]

private theorem rows_by_sum (u : Gaps) : SlabTables.rows u = rowsFor (4+tailSum u) := by
  have wt : ∀ z : Fin 7, (if z == 1 then 4 else if z == 2 then 1 else 0) = weight z.val := by decide
  have select (n : Nat) (A B C D : Array String) :
      (match n with | 12 => A | 9 => B | 6 => C | 5 => D | _ => #[]) =
        (if 4+n=16 then A else if 4+n=13 then B else if 4+n=10 then C else if 4+n=9 then D else #[]) := by
    by_cases a : n = 12
    · subst n; rfl
    by_cases b : n = 9
    · subst n; rfl
    by_cases c : n = 6
    · subst n; rfl
    by_cases d : n = 5
    · subst n; rfl
    split <;> try omega
    simp [show 4+n ≠ 16 by omega,show 4+n ≠ 13 by omega,show 4+n ≠ 10 by omega,show 4+n ≠ 9 by omega]
  simpa only [SlabTables.rows,SlabTables.sourceRows,wt,tailSum,rowsFor] using
    select (tailSum u) SlabData.rows MixedSlabData.rows1112 MixedSlabData.rows1122 MixedSlabData.rows1123

private theorem sorted_by_sum (u : Gaps) (valid : ∀ j, u.get j ∈ (#[1,2,3] : Array (Fin 7)))
    (admitted : tailSum u = 12 ∨ tailSum u = 9 ∨ tailSum u = 6 ∨ tailSum u = 5) :
    SlabTables.sortedProfile u = profileFor (4+tailSum u) := by
  have finite : ∀ a b c : Fin 7, (a=1 ∨ a=2 ∨ a=3) → (b=1 ∨ b=2 ∨ b=3) → (c=1 ∨ c=2 ∨ c=3) →
      let v : Gaps := #v[a,b,c]
      (tailSum v = 12 ∨ tailSum v = 9 ∨ tailSum v = 6 ∨ tailSum v = 5) →
        SlabTables.sortedProfile v = profileFor (4+tailSum v) := by decide +kernel
  have each (j : Fin 3) : u.get j = 1 ∨ u.get j = 2 ∨ u.get j = 3 := by simpa using valid j
  have repr : #v[u.get 0,u.get 1,u.get 2] = u := by
    apply Vector.ext
    intro i hi
    have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl|rfl|rfl <;> rfl
  simpa only [repr] using finite (u.get 0) (u.get 1) (u.get 2) (each 0) (each 1) (each 2) (by rw [repr]; exact admitted)

theorem rows_profile {m : Frame} (valid : ValidFrame m) (g : Isometry 4) (one : (FrameAction.moved g m).gap 0 = 1)
    (r : String) (hr : r ∈ SlabTables.rows (Scan.gapsOf (FrameAction.moved g m))) :
    r ∈ rowsFor (tally m) ∧ SlabTables.sortedProfile (Scan.gapsOf (FrameAction.moved g m)) = profileFor (tally m) ∧
      (tally m = 16 ∨ tally m = 13 ∨ tally m = 10 ∨ tally m = 9) := by
  let f := FrameAction.moved g m
  let u := Scan.gapsOf f
  have h := tally_eq m g valid one
  rw [rows_by_sum, ← h] at hr
  have keep : tally m = 16 ∨ tally m = 13 ∨ tally m = 10 ∨ tally m = 9 := by
    by_contra! bad
    simp [rowsFor,bad.1,bad.2.1,bad.2.2.1,bad.2.2.2] at hr
  refine ⟨hr,?_,keep⟩
  rw [h]
  apply sorted_by_sum _ (Scan.gaps_valid _ (fun j => valid (g.1 j)))
  omega

end SevenCycle.Adjacent.MixedCommon
