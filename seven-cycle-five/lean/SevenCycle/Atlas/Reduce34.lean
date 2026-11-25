import SevenCycle.Atlas.Patterns
import SevenCycle.Atlas.NormalizeCube

/-! Reduce the upper bound in the cube to its normalized 34-word plane chains. -/

namespace SevenCycle.Atlas

open Blueprint Proof CubePlanes

private theorem projected_card {C : Finset (Tuple 3)} (hc : packing cycleStep C) (i : ZMod 7) :
    (projectedBand C 0 i).card = (band C 0 i).card :=
  Finset.card_image_iff.mpr (Bands.band_projection hc 0 i).1

theorem card_le_thirty_three_of_normalized
    (planar : ∀ R : Finset (Tuple 2), packing cycleStep R → R.card = 10 →
      ∃ r : Fin 3, ∃ h : Isometry 2, R = actOnCode h (twoRepresentatives r))
    (exclude : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card = 34 →
      ∀ r : Fin 3, projectedBand D 0 0 = twoRepresentatives r →
      ∀ d : Fin 4, (∀ i, CubePlanes.deficit D i = pattern34 d i) → False)
    (C : Finset (Tuple 3)) (hc : packing cycleStep C) : C.card ≤ 33 := by
  by_contra! hbig
  obtain ⟨B, hBC, h34⟩ := Finset.exists_subset_card_eq (show 34 ≤ C.card by omega)
  have hB : packing cycleStep B := fun x hx y hy => hc x (hBC hx) y (hBC hy)
  obtain ⟨s, d, pat⟩ := canonical_pattern34 hB h34
  have firstZero : ∀ j : Fin 4, pattern34 j 0 = 0 := by decide
  have hs0 := pat 0
  rw [add_zero, firstZero] at hs0
  have ub : (band B 0 s).card ≤ 10 := Bands.band_card_le card_le_ten B hB 0 s
  have hten : (band B 0 s).card = 10 := by unfold CubePlanes.deficit at hs0; omega
  obtain ⟨g, r, hD, hsize, hrow, hbands⟩ := normalise_ten_band planar B hB 0 s hten
  let D := actOnCode (Crossings.liftAction 0 s g) B
  apply exclude D hD (hsize.trans h34) r hrow d
  intro i
  have he := hbands (s+i)
  rw [add_sub_cancel_left] at he
  have equiv_card := congrArg Finset.card he
  change (projectedBand D 0 i).card = ((projectedBand B 0 (s+i)).image (act g)).card at equiv_card
  rw [projected_card hD, Finset.card_image_of_injective _
    (Function.LeftInverse.injective (Symmetry.undo_act g)), projected_card hB] at equiv_card
  unfold CubePlanes.deficit
  rw [equiv_card]
  exact pat i

end SevenCycle.Atlas
