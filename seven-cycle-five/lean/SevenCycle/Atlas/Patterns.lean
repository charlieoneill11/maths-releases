import SevenCycle.Atlas.CubePlanes
import Mathlib.Data.Fin.VecNotation

/-! # The four cyclic window patterns for a putative 34-word code -/

namespace SevenCycle.Atlas.CubePlanes

open Blueprint Proof

/-- With only two deficit units, put one of them at the wraparound window 6.
The second can be three, two, one or zero starts earlier on the cycle. -/
def pattern34 (gap : Fin 4) (j : ZMod 7) : Nat :=
  (if j = 6 then 1 else 0) + (if j = (3 + (gap.val : ZMod 7)) then 1 else 0)

private def RotatesTo34 (v : ZMod 7 → Nat) : Prop :=
  ∃ s : ZMod 7, ∃ d : Fin 4, ∀ t : ZMod 7, v (s+t) = pattern34 d t

private instance (v : ZMod 7 → Nat) : Decidable (RotatesTo34 v) := by
  unfold RotatesTo34
  infer_instance

set_option maxRecDepth 10000 in
private theorem all_patterns34 :
    ∀ (a : Fin 3) (b : Fin (3-a.val)) (c : Fin (3-a.val-b.val))
      (d : Fin (3-a.val-b.val-c.val)) (e : Fin (3-a.val-b.val-c.val-d.val))
      (f : Fin (3-a.val-b.val-c.val-d.val-e.val)),
      RotatesTo34 ![a.val, b.val, c.val, d.val, e.val, f.val,
        2-a.val-b.val-c.val-d.val-e.val-f.val] := by decide +kernel

theorem canonical_pattern34 {C : Finset (Tuple 3)} (hc : packing cycleStep C)
    (hs : C.card = 34) :
    ∃ s : ZMod 7, ∃ d : Fin 4, ∀ t : ZMod 7, deficit C (s+t) = pattern34 d t := by
  let v := deficit C
  have hr := sum_deficits hc
  rw [hs, Deficits.sum_seven_at _ 0] at hr
  simp only [zero_add] at hr
  change (v 0 + (v 1 + (v 2 + (v 3 + (v 4 + (v 5 + v 6)))))) + 2*34 = 70 at hr
  have h := all_patterns34 ⟨v 0, by omega⟩ ⟨v 1, by dsimp; omega⟩ ⟨v 2, by dsimp; omega⟩
    ⟨v 3, by dsimp; omega⟩ ⟨v 4, by dsimp; omega⟩ ⟨v 5, by dsimp; omega⟩
  have hex : (![v 0, v 1, v 2, v 3, v 4, v 5, 2-v 0-v 1-v 2-v 3-v 4-v 5] :
      ZMod 7 → Nat) = v := by
    funext i
    fin_cases i <;> first | rfl | change 2-v 0-v 1-v 2-v 3-v 4-v 5 = v 6; omega
  rw [hex] at h
  exact h

end SevenCycle.Atlas.CubePlanes
