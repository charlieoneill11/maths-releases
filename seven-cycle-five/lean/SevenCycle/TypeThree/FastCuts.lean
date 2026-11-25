import SevenCycle.TypeThree.Join

/-! Pack the six marked cuts with row and column extractions on machine words.
For the two transverse directions each source plane contributes a seven-bit
line to the output, in the original physical coordinate order. -/

namespace SevenCycle.TypeThree
open Bitsets

private theorem shift7 : ∀ i : Fin 7, (7*i.val).toUInt64.toNat % 64 = 7*i.val := by decide
private theorem shift1 : ∀ i : Fin 7, i.val.toUInt64.toNat % 64 = i.val := by decide

private theorem sendLine_bit (v : UInt64) (i x y : Fin 7) :
    (sendLine v i).toNat.testBit (7*x.val+y.val) = (decide (i = x) && v.toNat.testBit y.val) := by
  have hx := x.isLt
  have hy := y.isLt
  have h64 : 7*x.val+y.val < 64 := by omega
  have hm : (127 : UInt64).toNat = 2^7-1 := by decide
  simp only [sendLine, UInt64.toNat_shiftLeft, shift7, Nat.testBit_mod_two_pow, h64, decide_true,
    Bool.true_and, Nat.testBit_shiftLeft, UInt64.toNat_and, Nat.testBit_and, hm,
    Nat.testBit_two_pow_sub_one]
  by_cases h : i = x
  · subst x
    simp [hy]
  · have hn : i.val ≠ x.val := fun e => h (Fin.ext e)
    by_cases hle : 7*i.val ≤ 7*x.val+y.val
    · have hdiff : ¬ (7*x.val+y.val - 7*i.val < 7) := by omega
      simp [hle, hdiff, h]
    · simp [hle, h]

private theorem joinLines_bit (f : Fin 7 → UInt64) (x y : Fin 7) :
    (joinLines f).toNat.testBit (7*x.val+y.val) = (f x).toNat.testBit y.val := by
  have unroll : joinLines f = sendLine (f 0) 0 ||| sendLine (f 1) 1 ||| sendLine (f 2) 2 |||
      sendLine (f 3) 3 ||| sendLine (f 4) 4 ||| sendLine (f 5) 5 ||| sendLine (f 6) 6 := by
    simp only [joinLines, sendLine]; rfl
  simp only [unroll, UInt64.toNat_or, Nat.testBit_or, sendLine_bit]
  fin_cases x <;> simp

private theorem gatherBit_bit (p : UInt64) (j y : Fin 7) :
    (gatherBit p j).toNat.testBit y.val = (decide (j = y) && p.toNat.testBit (7*y.val)) := by
  have h := y.isLt
  have h64 : y.val < 64 := by omega
  simp only [gatherBit, UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.testBit_and,
    Nat.testBit_shiftRight, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_two_pow,
    h64, decide_true, Bool.true_and]
  by_cases he : j = y
  · subst j
    simp [Nat.mod_eq_of_lt (show 6*y.val < 64 by omega), show 6*y.val+y.val = 7*y.val by omega]
  · have hn : j.val ≠ y.val := fun e => he (Fin.ext e)
    simp [hn, he]

private theorem gatherColumn_bit (p : UInt64) (y : Fin 7) :
    (gatherColumn p).toNat.testBit y.val = p.toNat.testBit (7*y.val) := by
  have unroll : gatherColumn p = gatherBit p 0 ||| gatherBit p 1 ||| gatherBit p 2 ||| gatherBit p 3 |||
      gatherBit p 4 ||| gatherBit p 5 ||| gatherBit p 6 := by
    simp only [gatherColumn, gatherBit]; rfl
  simp only [unroll, UInt64.toNat_or, Nat.testBit_or, gatherBit_bit]
  fin_cases y <;> simp

private theorem lineY_bit (p : UInt64) (s z : ZMod 7) :
    (lineY p s).toNat.testBit z.val = p.toNat.testBit (7*s.val+z.val) := by
  simp only [lineY, UInt64.toNat_shiftRight, Nat.testBit_shiftRight]
  rw [shift7 s]
  rfl

private theorem lineZ_bit (p : UInt64) (s y : ZMod 7) :
    (lineZ p s).toNat.testBit y.val = p.toNat.testBit (7*y.val+s.val) := by
  have gather (v : UInt64) : (gatherColumn v).toNat.testBit y.val = v.toNat.testBit (7*y.val) :=
    gatherColumn_bit v y
  rw [lineZ, gather, UInt64.toNat_shiftRight, Nat.testBit_shiftRight, Nat.add_comm]
  rw [shift1 s]
  rfl

private theorem lines_bit (f : Fin 7 → UInt64) (x y : ZMod 7) :
    (joinLines f).toNat.testBit (7*x.val+y.val) = (f x).toNat.testBit y.val := joinLines_bit f x y

private theorem insertX : ∀ (s : ZMod 7) (w : Proof.Tuple 2),
    (0 : Fin 3).insertNth (α := fun _ => ZMod 7) s w = ![s,w 0,w 1] := by decide
private theorem insertY : ∀ (s : ZMod 7) (w : Proof.Tuple 2),
    (1 : Fin 3).insertNth (α := fun _ => ZMod 7) s w = ![w 0,s,w 1] := by decide
private theorem insertZ : ∀ (s : ZMod 7) (w : Proof.Tuple 2),
    (2 : Fin 3).insertNth (α := fun _ => ZMod 7) s w = ![w 0,w 1,s] := by decide

private theorem cutX_eq (c : Cube) (s : ZMod 7) : cutX c s = cut c 0 s := by
  apply plane_eq_of_set_eq (canonical_clean _) (canonical_cut c 0 s)
  ext w
  simp only [mem_planeSet, planeMem_clean]
  simp only [cut, planeMem, UInt64.toNat_or, Nat.testBit_or]
  change _ ↔ (planeMem (lev c 0 s) w || planeMem (lev c 0 (s+1)) w) = true
  simp only [lev, planeMem_buildPlane, insertX]
  rfl

private theorem cutY_eq (c : Cube) (s : ZMod 7) : cutY c s = cut c 1 s := by
  apply plane_eq_of_set_eq (canonical_clean _) (canonical_cut c 1 s)
  ext w
  simp only [mem_planeSet, planeMem_clean]
  simp only [cut, planeMem, UInt64.toNat_or, Nat.testBit_or]
  change (joinLines _).toNat.testBit (7*(w 0 : Fin 7).val+(w 1 : Fin 7).val) = true ↔
    (planeMem (lev c 1 s) w || planeMem (lev c 1 (s+1)) w) = true
  rw [lines_bit _ (w 0) (w 1), UInt64.toNat_or, Nat.testBit_or]
  simp only [lev, planeMem_buildPlane, insertY, lineY_bit]
  rfl

private theorem cutZ_eq (c : Cube) (s : ZMod 7) : cutZ c s = cut c 2 s := by
  apply plane_eq_of_set_eq (canonical_clean _) (canonical_cut c 2 s)
  ext w
  simp only [mem_planeSet, planeMem_clean]
  simp only [cut, planeMem, UInt64.toNat_or, Nat.testBit_or]
  change (joinLines _).toNat.testBit (7*(w 0 : Fin 7).val+(w 1 : Fin 7).val) = true ↔
    (planeMem (lev c 2 s) w || planeMem (lev c 2 (s+1)) w) = true
  rw [lines_bit _ (w 0) (w 1), UInt64.toNat_or, Nat.testBit_or]
  simp only [lev, planeMem_buildPlane, insertZ, lineZ_bit]
  rfl

theorem fastCut_eq (c : Cube) (k : Fin 3) (s : ZMod 7) : fastCut c k s = cut c k s := by
  fin_cases k
  · exact cutX_eq c s
  · exact cutY_eq c s
  · exact cutZ_eq c s

theorem fastCutsOf_eq (c : Cube) : fastCutsOf c = cutsOf c := by
  simp only [fastCutsOf, cutsOf, cutX_eq, cutY_eq, cutZ_eq]
  rfl

end SevenCycle.TypeThree
