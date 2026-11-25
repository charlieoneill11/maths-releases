import SevenCycle.Atlas.Prefix
import SevenCycle.Atlas.WindowDP

namespace SevenCycle.Atlas.CubePlanes

open Proof Blueprint Bitsets Completions

/-- Each window incurs the larger of its orbit-table deficit and its
row-completion deficit. -/
@[inline] private def windowDeficit (last : Fin 7) (c : Cube) (k : Fin 3) (s : ZMod 7) : Nat :=
  let m := TypeThree.fastCut c k s
  max (if fullTable.contains m then 0 else 1) (10 - WindowDP.prefixBound last m)

@[inline] private def axisDeficit (last : Fin 7) (c : Cube) (k : Fin 3) : Nat :=
  let f := windowDeficit last c k
  f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + f 6)))))

def strongPrefix (budget : Nat) (last : Fin 7) (stack : Array Plane) : Bool :=
  let c := prefixCube stack
  decide (axisDeficit last c 1 ≤ budget) && decide (axisDeficit last c 2 ≤ budget)

private theorem axisDeficit_eq (last : Fin 7) (c : Cube) (k : Fin 3) :
    axisDeficit last c k = ∑ i : ZMod 7, windowDeficit last c k i := by
  rw [Deficits.sum_seven_at _ 0]
  simp [axisDeficit]

private theorem windowDeficit_bound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hC : packing cycleStep C) (last : Fin 7) (c : Cube)
    (k : Fin 3) (s : ZMod 7)
    (geom : planeSet (TypeThree.fastCut c k s) =
      (projectedBand C k s).filter (fun w => (w 0).val ≤ last.val)) :
    windowDeficit last c k s + (band C k s).card ≤ 10 := by
  have hle := Bands.band_card_le card_le_ten C hC k s
  obtain ⟨inj, hc⟩ := Bands.band_projection hC k s
  have hcard : (projectedBand C k s).card = (band C k s).card := Finset.card_image_iff.mpr inj
  have dp := WindowDP.prefixBound_sound _ hc last _ geom
  have hit (hfull : (band C k s).card = 10) :
      fullTable.contains (TypeThree.fastCut c k s) = true := by
    obtain ⟨m, hm, hmask⟩ := Planar.maxMasks_complete hplan _ hc (hcard.trans hfull)
    apply fullTable_contains m _ hm (TypeThree.fastCut_eq c k s ▸ canonical_cut c k s)
    rw [geom, hmask]
    exact Finset.filter_subset _ _
  change (projectedBand C k s).card ≤ _ at dp
  rw [hcard] at dp
  change (band C k s).card ≤ 10 at hle
  dsimp only [windowDeficit]
  by_cases hfull : (band C k s).card = 10
  · rw [if_pos (hit hfull)]
    omega
  · split <;> omega

/-- The partial cut supplies exactly the first rows of the actual transverse
window, so neither pruning bound can overstate its eventual deficit. -/
theorem strongPrefix_sound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hC : packing cycleStep C) {budget : Nat}
    (hbudget : 70 ≤ 2*C.card + budget) {last : Fin 7} {stack : Array Plane}
    (geom : ∀ k : Fin 3, k ≠ 0 → ∀ s, planeSet (TypeThree.fastCut (prefixCube stack) k s) =
      (projectedBand C k s).filter (fun w => (w 0).val ≤ last.val)) :
    strongPrefix budget last stack = true := by
  have axis (k : Fin 3) (hk : k ≠ 0) : axisDeficit last (prefixCube stack) k ≤ budget := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      windowDeficit_bound hplan hC last _ k i (geom k hk i))
    have hb : ∑ i : ZMod 7, (band C k i).card = 2*C.card := Bands.sum_band_card C k
    rw [Finset.sum_add_distrib, hb] at hsum
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hsum
    rw [axisDeficit_eq]
    omega
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (axis 1 (by decide)), decide_eq_true (axis 2 (by decide))⟩

end SevenCycle.Atlas.CubePlanes
