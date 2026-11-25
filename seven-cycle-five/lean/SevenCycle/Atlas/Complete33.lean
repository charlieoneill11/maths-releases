import SevenCycle.Atlas.StrongCheck
import SevenCycle.Atlas.Patterns33
import SevenCycle.Atlas.Leaves

/-! # From normalized cube searches to the completeness of the released atlas -/

namespace SevenCycle.Atlas

open Blueprint Proof CubePlanes
open Bitsets (planeCard)

/-- Apply h first, then g, with both motions in the signed affine representation. -/
private def compose {n : Nat} (g h : Isometry n) : Isometry n :=
  (g.1.trans h.1, fun i => g.2.1 i ^^ h.2.1 (g.1 i),
   fun i => (if g.2.1 i then -h.2.2 (g.1 i) else h.2.2 (g.1 i)) + g.2.2 i)

private theorem compose_act {n : Nat} (g h : Isometry n) (x : Tuple n) :
    act (compose g h) x = act g (act h x) := by
  funext i
  simp only [act, compose, Equiv.trans_apply]
  cases s : g.2.1 i <;> cases t : h.2.1 (g.1 i) <;> simp [add_comm,add_left_comm]

def classify33Check (jobs : Array (Fin 3 × Fin 30)) : Bool :=
  jobs.all fun (r,p) => normalizedCheckUsing (strongPrune 4) r 3 (pattern33 p) Leaves.atlasLeaf

/-- Search chunks separate the expensive low-index deficit patterns. -/
def jobs33 (r : Fin 3) (g : Fin 8) : Array (Fin 3 × Fin 30) :=
  let ps : Array (Fin 30) := match g.val with
    | 0 => #[0, 1]
    | 1 => #[2]
    | 2 => #[3]
    | 3 => #[4]
    | 4 => #[5, 6, 7, 8, 9]
    | 5 => #[10, 11, 12, 13, 14]
    | 6 => #[15, 16, 17, 18, 19, 20, 21]
    | _ => #[22, 23, 24, 25, 26, 27, 28, 29]
  ps.map (fun p => (r,p))

theorem jobs33_cover : ∀ (r : Fin 3) (p : Fin 30), ∃ g : Fin 8, (r,p) ∈ jobs33 r g := by decide +kernel

theorem atlas_complete_of_jobs (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    (checks : ∀ (r : Fin 3) (p : Fin 30), ∃ jobs : Array (Fin 3 × Fin 30), (r,p) ∈ jobs ∧ classify33Check jobs = true)
    (C : Finset (Tuple 3)) (hc : packing cycleStep C) (hs : C.card = 33) :
    ∃ r : Fin atlasPlanes.size, ∃ g : Isometry 3, C = actOnCode g (atlasRepresentative r) := by
  obtain ⟨s,p,pat⟩ := canonical_pattern33 hc hs
  have hzero := pat 0
  rw [add_zero, pattern33_first] at hzero
  have ub : (band C 0 s).card ≤ 10 := Bands.band_card_le card_le_ten C hc 0 s
  have h10 : (band C 0 s).card = 10 := by unfold CubePlanes.deficit at hzero; omega
  obtain ⟨g,r,hD,hcard,hn,hbands⟩ :=
    normalise_ten_band (Planar.classificationCheck_sound _ hplan) C hc 0 s h10
  let γ := Crossings.liftAction 0 s g
  let D := actOnCode γ C
  have hcD : D.card = 33 := hcard.trans hs
  have hd (i : ZMod 7) : CubePlanes.deficit D i = pattern33 p i := by
    have he := hbands (s+i)
    rw [add_sub_cancel_left] at he
    have hh := congrArg Finset.card he
    change (projectedBand D 0 i).card = ((projectedBand C 0 (s+i)).image (act g)).card at hh
    have proj {F : Finset (Tuple 3)} (hF : packing cycleStep F) (j : ZMod 7) :
        (projectedBand F 0 j).card = (band F 0 j).card :=
      Finset.card_image_iff.mpr (Bands.band_projection hF 0 j).1
    rw [proj hD, Finset.card_image_of_injective _ (Function.LeftInverse.injective (Symmetry.undo_act g)),
      proj hc] at hh
    unfold CubePlanes.deficit
    rw [hh]
    exact pat i
  have pop (t : ZMod 7) : planeCard (plane D t) = population 3 (pattern33 p) t := by
    have h := plane_population hD t
    change planeCard (plane D t) + 30 = D.card + CubePlanes.deficit D (t+1) +
      CubePlanes.deficit D (t+3) + CubePlanes.deficit D (t+5) at h
    simp only [hd, hcD] at h
    unfold population
    omega
  obtain ⟨jobs,hm,ok⟩ := checks r p
  have okrp : normalizedCheckUsing (strongPrune 4) r 3 (pattern33 p) Leaves.atlasLeaf = true := by
    unfold classify33Check at ok
    exact Array.all_eq_true'.mp ok (r,p) hm
  have hb : 70 ≤ 2*D.card+4 := by omega
  have hLeaf : Leaves.atlasLeaf (prefixCube (initialPlanes D 7)) = true := normalizedCheckUsing_sound hplan hD r hn (strongPrune 4) 3 (pattern33 p)
    (fun j => strongPrune_sound hplan hD hb j) pop hd Leaves.atlasLeaf okrp
  obtain ⟨row,motion,he⟩ := Leaves.atlasLeaf_sound _ hLeaf
  rw [initialPlanes_complete] at he
  change D = actOnCode motion (atlasRepresentative row) at he
  refine ⟨row, compose (Symmetry.undo γ) motion, ?_⟩
  calc
    C = actOnCode (Symmetry.undo γ) D := by
      unfold D actOnCode
      rw [Finset.image_image, show act (Symmetry.undo γ) ∘ act γ = id from funext (Symmetry.undo_act γ), Finset.image_id]
    _ = actOnCode (Symmetry.undo γ) (actOnCode motion (atlasRepresentative row)) := congrArg _ he
    _ = actOnCode (compose (Symmetry.undo γ) motion) (atlasRepresentative row) := by
      unfold actOnCode
      rw [Finset.image_image]
      exact Finset.image_congr fun x _ => (compose_act ..).symm

end SevenCycle.Atlas
