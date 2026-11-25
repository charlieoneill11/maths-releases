import SevenCycle.Bitsets.Counts
import SevenCycleRuntime.Adjacent

/-!
# Support pairs for adjacent full bands

Each seven-bit table lookup counts one row of a plane. The support test uses
the 49 bits representing torus points and ignores the unused high bits.
-/

namespace SevenCycle.Adjacent

open Bitsets

open SevenCycleRuntime.Adjacent (rowWeights rowIndex rowWeight)
abbrev maskCard := SevenCycleRuntime.Adjacent.maskCard

private theorem bitCount_congr {m n : Nat} (x : BitVec m) (y : BitVec n) (k : Nat)
    (h : ∀ i < k, x.getLsbD i = y.getLsbD i) : x.cpopNatRec k 0 = y.cpopNatRec k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [BitVec.cpopNatRec_succ, zero_add]
    rw [BitVec.cpopNatRec_eq, BitVec.cpopNatRec_eq (x := y), h k (by omega), ih (fun i hi => h i (by omega))]

private theorem bitCount_split {w : Nat} (x : BitVec w) (k n : Nat) :
    x.cpopNatRec (k+n) 0 = x.cpopNatRec k 0 + (x >>> k).cpopNatRec n 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq (x := x),
      BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq (x := x >>> k), ih]
    simp [Nat.add_assoc]

private theorem rowWeight_eq (p : UInt64) (offset : UInt64) :
    rowWeight p offset = (p.toBitVec >>> (offset.toNat % 64)).cpopNatRec 7 0 := by
  unfold rowWeight rowWeights
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  apply bitCount_congr
  intro j hj
  change (BitVec.ofNat 7 ((p >>> offset) &&& (127 : UInt64)).toNat).getLsbD j = _
  rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and, UInt64.toNat_and,
    Nat.testBit_and, UInt64.toNat_shiftRight, Nat.testBit_shiftRight, BitVec.getLsbD_ushiftRight]
  have hm : (127 : UInt64).toNat.testBit j = true := by
    change (2^7 - 1 : Nat).testBit j = true
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hj
  rw [hm, Bool.and_true]; rfl

theorem maskCard_eq (p : UInt64) : maskCard p = planeCard p := by
  by_cases h : p = 0
  · subst p; rfl
  simp only [maskCard, SevenCycleRuntime.Adjacent.maskCard, if_neg h, rowWeight_eq, planeCard]
  rw [bitCount_split p.toBitVec 42 7, bitCount_split p.toBitVec 35 7,
    bitCount_split p.toBitVec 28 7, bitCount_split p.toBitVec 21 7,
    bitCount_split p.toBitVec 14 7, bitCount_split p.toBitVec 7 7]
  simp


abbrev SupportCube := SevenCycleRuntime.Adjacent.SupportCube

def pack (a : Cube) : SupportCube :=
  ⟨a.get 0, a.get 1, a.get 2, a.get 3, a.get 4, a.get 5, a.get 6⟩

abbrev overlap := SevenCycleRuntime.Adjacent.overlap

theorem overlap_eq (s t : Cube) :
    overlap (pack s) (pack t) = (cubeSet s ∩ cubeSet t).card := by
  rw [← cubeSet_inter, ← cubeCard_eq]
  simp only [overlap, SevenCycleRuntime.Adjacent.overlap, pack, maskCard_eq, cubeCard]
  simp [cubeInter, Vector.get]

abbrev checkSupports := SevenCycleRuntime.Adjacent.checkSupports

/-- Any genuine middle layer is contained in both normalized supports. If its
size is at least 16, the continuation for this pair must have succeeded. -/
theorem checkSupports_sound {anchors images : Array SupportCube}
    {next : SupportCube → SupportCube → Bool}
    (ok : checkSupports anchors images next = true) {s t : Cube}
    (hs : pack s ∈ anchors) (ht : pack t ∈ images)
    {U : Finset (Proof.Tuple 3)} (hU : U ⊆ cubeSet s ∩ cubeSet t) (h16 : 16 ≤ U.card) :
    next (pack s) (pack t) = true := by
  have hst := Array.all_eq_true_iff_forall_mem.mp
    (Array.all_eq_true_iff_forall_mem.mp ok (pack t) ht) (pack s) hs
  have hsize : 16 ≤ overlap (pack s) (pack t) := (overlap_eq s t).symm ▸
    h16.trans (Finset.card_le_card hU)
  simpa only [Bool.or_eq_true, decide_eq_true_eq, Nat.not_lt.mpr hsize, false_or] using hst

end SevenCycle.Adjacent
