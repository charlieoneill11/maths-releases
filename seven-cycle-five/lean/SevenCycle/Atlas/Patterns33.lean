import SevenCycle.Atlas.Patterns
import SevenCycle.Atlas.NormalizeCube

/-! # The thirty rotations of a cube deficit sequence of sum four -/

namespace SevenCycle.Atlas.CubePlanes

open Proof Blueprint

/-- Every cyclic rotation class has one lexicographically least sequence.
Rows list the weak compositions of four that satisfy this convention. -/
def patterns33 : Vector (Vector Nat 7) 30 := #v[
  #v[0, 1, 0, 1, 0, 1, 1],
  #v[0, 0, 2, 0, 1, 0, 1],
  #v[0, 0, 1, 1, 1, 0, 1],
  #v[0, 0, 1, 1, 0, 1, 1],
  #v[0, 0, 1, 1, 0, 0, 2],
  #v[0, 0, 1, 0, 2, 0, 1],
  #v[0, 0, 1, 0, 1, 1, 1],
  #v[0, 0, 1, 0, 1, 0, 2],
  #v[0, 0, 1, 0, 0, 2, 1],
  #v[0, 0, 1, 0, 0, 1, 2],
  #v[0, 0, 0, 3, 0, 0, 1],
  #v[0, 0, 0, 2, 1, 0, 1],
  #v[0, 0, 0, 2, 0, 1, 1],
  #v[0, 0, 0, 2, 0, 0, 2],
  #v[0, 0, 0, 1, 2, 0, 1],
  #v[0, 0, 0, 1, 1, 1, 1],
  #v[0, 0, 0, 1, 1, 0, 2],
  #v[0, 0, 0, 1, 0, 2, 1],
  #v[0, 0, 0, 1, 0, 1, 2],
  #v[0, 0, 0, 1, 0, 0, 3],
  #v[0, 0, 0, 0, 3, 0, 1],
  #v[0, 0, 0, 0, 2, 1, 1],
  #v[0, 0, 0, 0, 2, 0, 2],
  #v[0, 0, 0, 0, 1, 2, 1],
  #v[0, 0, 0, 0, 1, 1, 2],
  #v[0, 0, 0, 0, 1, 0, 3],
  #v[0, 0, 0, 0, 0, 3, 1],
  #v[0, 0, 0, 0, 0, 2, 2],
  #v[0, 0, 0, 0, 0, 1, 3],
  #v[0, 0, 0, 0, 0, 0, 4]]

def pattern33 (p : Fin 30) (t : ZMod 7) : Nat := (patterns33.get p).get t

private def RotatesTo33 (v : ZMod 7 → Nat) : Prop :=
  ∃ s : ZMod 7, ∃ p : Fin 30, ∀ t : ZMod 7, v (s+t) = pattern33 p t

private instance (v : ZMod 7 → Nat) : Decidable (RotatesTo33 v) := by
  unfold RotatesTo33
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem all_patterns33 :
    ∀ (a : Fin 5) (b : Fin (5-a.val)) (c : Fin (5-a.val-b.val))
      (d : Fin (5-a.val-b.val-c.val)) (e : Fin (5-a.val-b.val-c.val-d.val))
      (f : Fin (5-a.val-b.val-c.val-d.val-e.val)),
      RotatesTo33 ![a.val, b.val, c.val, d.val, e.val, f.val,
        4-a.val-b.val-c.val-d.val-e.val-f.val] := by decide +kernel

theorem canonical_pattern33 {C : Finset (Tuple 3)} (hc : packing cycleStep C)
    (hs : C.card = 33) :
    ∃ s : ZMod 7, ∃ p : Fin 30, ∀ t : ZMod 7, deficit C (s+t) = pattern33 p t := by
  let v := deficit C
  have hr := sum_deficits hc
  rw [hs, Deficits.sum_seven_at _ 0] at hr
  simp only [zero_add] at hr
  change (v 0 + (v 1 + (v 2 + (v 3 + (v 4 + (v 5 + v 6)))))) + 2*33 = 70 at hr
  have h := all_patterns33 ⟨v 0, by omega⟩ ⟨v 1, by dsimp; omega⟩ ⟨v 2, by dsimp; omega⟩
    ⟨v 3, by dsimp; omega⟩ ⟨v 4, by dsimp; omega⟩ ⟨v 5, by dsimp; omega⟩
  have hex : (![v 0, v 1, v 2, v 3, v 4, v 5, 4-v 0-v 1-v 2-v 3-v 4-v 5] :
      ZMod 7 → Nat) = v := by
    funext i
    fin_cases i <;> first | rfl | change 4-v 0-v 1-v 2-v 3-v 4-v 5 = v 6; omega
  rw [hex] at h
  exact h

theorem pattern33_first : ∀ p, pattern33 p 0 = 0 := by decide +kernel

end SevenCycle.Atlas.CubePlanes
