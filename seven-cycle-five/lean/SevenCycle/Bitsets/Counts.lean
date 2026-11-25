import SevenCycle.Proof.Bitsets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Population counts and tests for adjacent planes. -/

namespace SevenCycle.Bitsets
open Proof (Tuple cycleStep)

/-- A population count restricted to the 49 sites of a plane. -/
@[inline] def planeCard (p : Plane) : Nat := p.toBitVec.cpopNatRec 49 0

private theorem countRange (p : Plane) (n : Nat) :
    p.toBitVec.cpopNatRec n 0 = ((Finset.range n).filter (p.toNat.testBit ·)).card := by
  induction n with
  | zero => simp [BitVec.cpopNatRec]
  | succ n ih =>
    rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq, ih]
    change _ + (0 + (p.toNat.testBit n).toNat) = _
    rw [Finset.range_add_one]
    cases h : p.toNat.testBit n <;> simp [Finset.filter_insert, h]

theorem planeCard_eq (p : Plane) : planeCard p = (planeSet p).card := by
  rw [planeCard, countRange]
  refine Finset.card_bij' (fun i _ => pointAt i) (fun x _ => index x) ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨hir, hb⟩ := Finset.mem_filter.mp hi
    simpa [planeMem, index_pointAt ⟨i, Finset.mem_range.mp hir⟩] using hb
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (index_lt x), (mem_planeSet p x).mp hx⟩
  · intro i hi
    exact index_pointAt ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩
  · intro x _; exact pointAt_index x

/-- Seven additions, without constructing a Finset of words. -/
@[inline] def cubeCard (c : Cube) : Nat :=
  planeCard (c.get 0) + planeCard (c.get 1) + planeCard (c.get 2) + planeCard (c.get 3) +
    planeCard (c.get 4) + planeCard (c.get 5) + planeCard (c.get 6)

private theorem fiberCard (c : Cube) (i : Fin 7) :
    ((cubeSet c).filter fun x => x 0 = i).card = (planeSet (c.get i)).card := by
  refine Finset.card_bij' (fun x _ => Fin.tail x) (fun y _ => Fin.cons (i : ZMod 7) y) ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hw
    change Fin.tail w ∈ planeSet (c.get i)
    rw [← hi]
    exact (mem_planeSet ..).mpr ((mem_cubeSet ..).mp hc)
  · intro y hy
    exact Finset.mem_filter.mpr ⟨(mem_cubeSet ..).mpr ((mem_planeSet ..).mp hy), rfl⟩
  · intro x hx
    change Fin.cons (i : ZMod 7) (Fin.tail x) = x
    rw [← (Finset.mem_filter.mp hx).2]
    exact Fin.cons_self_tail x
  · intro y _; exact Fin.tail_cons ..

theorem cubeCard_eq (c : Cube) : cubeCard c = (cubeSet c).card := by
  calc
    cubeCard c = ∑ i : Fin 7, planeCard (c.get i) := by
      simp [cubeCard, Fin.sum_univ_succ, Nat.add_assoc]
    _ = ∑ i : Fin 7, ((cubeSet c).filter fun x => (x 0 : Fin 7) = i).card := by
      apply Finset.sum_congr rfl
      intro i _
      exact (planeCard_eq _).trans (fiberCard c i).symm
    _ = _ := (Finset.card_eq_sum_card_fiberwise (f := fun x : Tuple 3 => (x 0 : Fin 7))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

/-- Test all conflicts between consecutive planes by one neighbourhood operation. -/
@[inline] def compatible (p q : Plane) : Bool := (p &&& neighbourhood q) == 0

private theorem planeSet_zero : planeSet 0 = ∅ := by ext x; simp [planeMem]

private theorem canonical_neighbourhood (p : Plane) : Canonical (neighbourhood p) :=
  canonical_clean _

theorem compatible_iff (p q : Plane) : compatible p q ↔
    ∀ x ∈ planeSet p, ∀ y ∈ planeSet q, ¬ ∀ i, cycleStep (x i) (y i) := by
  have hc : Canonical (p &&& neighbourhood q) := by
    intro i hi
    simp [canonical_neighbourhood q i hi]
  have hz : Canonical 0 := by intro i _; simp
  rw [compatible, beq_iff_eq]
  constructor
  · intro h x hx y hy hxy
    have hn := (mem_neighbourhood q x).mpr ⟨y, hy, hxy⟩
    have : x ∈ planeSet (p &&& neighbourhood q) := by simpa using Finset.mem_inter.mpr ⟨hx, hn⟩
    simp [h, planeSet_zero] at this
  · intro h
    apply plane_eq_of_set_eq hc hz
    rw [planeSet_zero, planeSet_and, ← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro x hx hn
    obtain ⟨y, hy, hxy⟩ := (mem_neighbourhood q x).mp hn
    exact h x hx y hy hxy

end SevenCycle.Bitsets
