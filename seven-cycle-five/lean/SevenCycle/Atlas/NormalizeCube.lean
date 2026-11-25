import SevenCycle.Proof.Crossings

/-! Coordinate normalization for enumerating cube codes starting at a ten-point band. -/

namespace SevenCycle.Atlas

open Blueprint Proof Proof.Crossings

/-- Lifting a planar isometry to the transverse coordinates transports all
parallel bands and shifts their start by the same chosen amount. -/
theorem projectedBand_lift {n : ℕ} (C : Finset (Tuple (n+1)))
    (k : Fin (n+1)) (i a : ZMod 7) (g : Isometry n) :
    projectedBand (actOnCode (liftAction k i g) C) 0 (a-i) =
      actOnCode g (projectedBand C k a) := by
  let γ := liftAction k i g
  have hb := image_band C γ 0 a
  have axis : γ.1 0 = k := by simp [γ, liftAction, liftPerm]
  have shift : startValue (γ.2.1 0) (γ.2.2 0) a = a-i := by
    simp [γ, liftAction, startValue, sub_eq_add_neg]
  rw [axis, shift] at hb
  unfold projectedBand
  rw [hb, Finset.image_image]
  change _ = ((band C k a).image (dropCoord k)).image (act g)
  rw [Finset.image_image]
  exact Finset.image_congr fun x _ => (liftAction_spec k i g x).2

/-- Once a ten-point band is chosen, the first projected band can be
identified with a specific one of the three literal planar representatives. -/
theorem normalise_ten_band
    (planar : ∀ R : Finset (Tuple 2), packing cycleStep R → R.card = 10 →
      ∃ r : Fin 3, ∃ h : Isometry 2, R = actOnCode h (twoRepresentatives r))
    (C : Finset (Tuple 3)) (hC : packing cycleStep C) (k : Fin 3)
    (i : ZMod 7) (h10 : (band C k i).card = 10) :
    ∃ g : Isometry 2, ∃ r : Fin 3,
      let γ := liftAction k i g
      let D := actOnCode γ C
      packing cycleStep D ∧ D.card = C.card ∧ projectedBand D 0 0 = twoRepresentatives r ∧
      (∀ a, projectedBand D 0 (a-i) = actOnCode g (projectedBand C k a)) := by
  obtain ⟨hi, hc⟩ := Bands.band_projection hC k i
  obtain ⟨r, h, hrow⟩ := planar _ hc ((Finset.card_image_iff.mpr hi).trans h10)
  let g := Symmetry.undo h
  let γ := liftAction k i g
  refine ⟨g, r, ?_, Finset.card_image_of_injective _ (Function.LeftInverse.injective (Symmetry.undo_act γ)),
    ?_, fun a => projectedBand_lift C k i a g⟩
  · intro x hx y hy hedge
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hC a ha b hb ((Symmetry.act_confusable γ a b).mp hedge)
  · have hp := projectedBand_lift C k i i g
    rw [sub_self] at hp
    rw [hp]
    change projectedBand C k i = _ at hrow
    rw [hrow]
    unfold actOnCode
    have hl : Function.LeftInverse (act g) (act h) := Symmetry.undo_act h
    rw [Finset.image_image, hl.comp_eq_id, Finset.image_id]

end SevenCycle.Atlas
