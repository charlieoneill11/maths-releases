import SevenCycle.Atlas.SmallBounds
import SevenCycle.Bitsets.Counts
import SevenCycle.Proof.Deficits

/-! # Plane chains for the cubical atlas

Dropping the first coordinate decomposes a code into seven planar codes.
Consecutive planes are compatible. Their sizes are determined by the seven
deficits and the size of the full cube.
-/

namespace SevenCycle.Atlas.CubePlanes

open Proof Blueprint Bitsets

/-- The points of C at first-coordinate height i, in the canonical planar mask. -/
def plane (C : Finset (Tuple 3)) (i : ZMod 7) : Plane :=
  buildPlane fun y => decide (Fin.cons i y ∈ C)

@[simp] theorem mem_plane (C : Finset (Tuple 3)) (i : ZMod 7) (y : Tuple 2) :
    y ∈ planeSet (plane C i) ↔ Fin.cons i y ∈ C := by
  simp [plane]

theorem plane_card (C : Finset (Tuple 3)) (i : ZMod 7) :
    planeCard (plane C i) = (level C 0 i).card := by
  rw [planeCard_eq]
  refine Finset.card_bij' (fun y _ => Fin.cons i y) (fun x _ => Fin.tail x) ?_ ?_ ?_ ?_
  · intro y hy
    exact Finset.mem_filter.mpr ⟨(mem_plane ..).mp hy, rfl⟩
  · intro x hx
    change Fin.tail x ∈ planeSet (plane C i)
    rw [mem_plane, ← (Finset.mem_filter.mp hx).2, Fin.cons_self_tail]
    exact (Finset.mem_filter.mp hx).1
  · intro y _; exact Fin.tail_cons ..
  · intro x hx
    change Fin.cons i (Fin.tail x) = x
    rw [← (Finset.mem_filter.mp hx).2, Fin.cons_self_tail]

theorem plane_code {C : Finset (Tuple 3)} (hc : packing cycleStep C) (i : ZMod 7) :
    packing cycleStep (planeSet (plane C i)) := by
  intro x hx y hy h
  apply hc _ ((mem_plane ..).mp hx) _ ((mem_plane ..).mp hy)
  refine ⟨fun e => h.1 (by simpa using congrArg Fin.tail e), ?_⟩
  intro k
  cases k using Fin.cases with
  | zero => simp [cycleStep]
  | succ k => exact h.2 k

theorem adjacent_compatible {C : Finset (Tuple 3)} (hc : packing cycleStep C) (i : ZMod 7) :
    compatible (plane C i) (plane C (i+1)) := by
  apply (compatible_iff ..).mpr
  intro x hx y hy hxy
  apply hc _ ((mem_plane ..).mp hx) _ ((mem_plane ..).mp hy)
  refine ⟨?_, ?_⟩
  · intro e
    have hz : i = i+1 := congrFun e 0
    have : (0 : ZMod 7) = 1 := add_left_cancel (by simpa using hz : i+0 = i+1)
    exact (by decide : (0 : ZMod 7) ≠ 1) this
  · intro k
    cases k using Fin.cases with
    | zero => simp [cycleStep]
    | succ k => exact hxy k

def deficit (C : Finset (Tuple 3)) (i : ZMod 7) : ℕ := 10 - (band C 0 i).card

private theorem deficit_add_band {C : Finset (Tuple 3)} (hc : packing cycleStep C)
    (i : ZMod 7) : deficit C i + (band C 0 i).card = 10 :=
  Nat.sub_add_cancel (Bands.band_card_le card_le_ten C hc 0 i)

theorem sum_deficits {C : Finset (Tuple 3)} (hc : packing cycleStep C) :
    (∑ i, deficit C i) + 2*C.card = 70 := by
  have hsum : ∑ i : ZMod 7, (deficit C i + (band C 0 i).card) = 70 := by
    simp [deficit_add_band hc, ZMod.card]
  rw [Finset.sum_add_distrib] at hsum
  exact (show ∑ i : ZMod 7, (band C 0 i).card = 2*C.card from Bands.sum_band_card C 0) ▸ hsum

theorem plane_population {C : Finset (Tuple 3)} (hc : packing cycleStep C) (i : ZMod 7) :
    planeCard (plane C i) + 30 = C.card + deficit C (i+1) + deficit C (i+3) + deficit C (i+5) := by
  rw [plane_card]
  have levels : ∑ j : ZMod 7, (level C 0 j).card = C.card := Bands.sum_level_card C 0
  rw [Deficits.sum_seven_at _ i] at levels
  have a := deficit_add_band hc (i+1)
  have b := deficit_add_band hc (i+3)
  have c := deficit_add_band hc (i+5)
  have hb (j : ZMod 7) : (band C 0 j).card = (level C 0 j).card + (level C 0 (j+1)).card :=
    Bands.band_card C 0 j
  simp only [hb, add_assoc] at a b c
  norm_num at a b c
  omega

theorem has_full_start {C : Finset (Tuple 3)} (hc : packing cycleStep C) (h : 33 ≤ C.card) :
    ∃ i, (band C 0 i).card = 10 := by
  by_contra! hn
  have hsum := Bands.sum_band_card C 0
  have hle : ∑ i : ZMod 7, (band C 0 i).card ≤ ∑ _ : ZMod 7, 9 := by
    apply Finset.sum_le_sum
    intro i _
    have hu := Bands.band_card_le card_le_ten C hc 0 i
    have hi := hn i
    change (band C 0 i).card ≤ 10 at hu
    omega
  change ∑ i : ZMod 7, (band C 0 i).card = 2*C.card at hsum
  simp [ZMod.card] at hle
  omega

end SevenCycle.Atlas.CubePlanes
