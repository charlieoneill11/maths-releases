import SevenCycle.TypeThree.Index
import SevenCycle.TypeThree.Exclusion

/-! # A complete check on an explicit block of representatives

Each source row expands to its 343 translations. Each domain row expands to
all 16,464 motions, including stabilizer repetitions. A checker can substitute
a faster signature once it proves that all six fields agree with `cutsOf`. -/

namespace SevenCycle.TypeThree
open Blueprint Proof

structure Block where
  sources : Array Bitsets.Cube
  domain : Array Bitsets.Cube
  firstSlot : Fin 6
  secondSlot : Fin 6

def signatures (representatives : Array Bitsets.Cube)
    (images : Bitsets.Cube → Array Bitsets.Cube) (signature : Bitsets.Cube → CutRow) :
    Array CutRow :=
  representatives.flatMap fun r => (images r).map signature

def checkBlock (signature : Bitsets.Cube → CutRow) (data : Block) : Bool :=
  checkSources (signatures data.sources Bitsets.translationImages signature)
    (signatures data.domain Bitsets.orbitImages signature) data.firstSlot data.secondSlot

private theorem signature_mem (h : ∀ w, signature w = cutsOf w)
    {reps : Array Bitsets.Cube} {r w : Bitsets.Cube} (hr : r ∈ reps)
    {images : Bitsets.Cube → Array Bitsets.Cube} (hw : w ∈ images r) :
    cutsOf w ∈ signatures reps images signature :=
  Array.mem_flatMap.mpr ⟨r, hr, Array.mem_map.mpr ⟨w, hw, h w⟩⟩

/-- An actual band is in the table whenever its orbit representative is in the
domain. This version works for partial input, without an atlas axiom. -/
def InOrbit (reps : Array Bitsets.Cube) (D : Finset (Tuple 3)) : Prop :=
  ∃ r ∈ reps, ∃ g : Isometry 3, D = (Bitsets.cubeSet r).image (Bitsets.wordEquiv g)

def IsSource (reps : Array Bitsets.Cube) (D : Finset (Tuple 3)) : Prop :=
  ∃ r ∈ reps, ∃ v : Tuple 3,
    D = (Bitsets.cubeSet r).image (Bitsets.wordEquiv (translation v))

theorem checkBlock_sound (signature : Bitsets.Cube → CutRow) (hσ : ∀ w, signature w = cutsOf w)
    (data : Block) (h : checkBlock signature data = true) (C : Finset (Tuple 4))
    (hs : IsSource data.sources (projectedBand C 0 0))
    (ht : InOrbit data.domain (projectedBand C 0 3))
    (htrans : ∀ k : Fin 4, k ≠ 0 → ∀ t : ZMod 7, (t = 0 ∨ t = 3) →
      InOrbit data.domain (projectedBand C k t)) : False := by
  obtain ⟨r, hr, v, hv⟩ := hs
  obtain ⟨s, hsm, hS⟩ := Bitsets.translationImages_complete v r
  have helper (k : Fin 4) (h : ZMod 7) (hw : InOrbit data.domain (projectedBand C k h)) :
      ∃ w, RepresentsBand C k h w ∧
        cutsOf w ∈ signatures data.domain Bitsets.orbitImages signature := by
    obtain ⟨r, hr, g, hrep⟩ := hw
    obtain ⟨w, hm, he⟩ := Bitsets.orbitImages_complete g r
    exact ⟨w, he.trans hrep.symm, signature_mem hσ hr hm⟩
  obtain ⟨t, hT, hmT⟩ := helper _ _ ht
  obtain ⟨a, hA, hmA⟩ := helper _ _ (htrans 1 (by decide) 0 (Or.inl rfl))
  obtain ⟨a', hA', hmA'⟩ := helper _ _ (htrans 1 (by decide) 3 (Or.inr rfl))
  obtain ⟨b, hB, hmB⟩ := helper _ _ (htrans 2 (by decide) 0 (Or.inl rfl))
  obtain ⟨b', hB', hmB'⟩ := helper _ _ (htrans 2 (by decide) 3 (Or.inr rfl))
  obtain ⟨c, hC, hmC⟩ := helper _ _ (htrans 3 (by decide) 0 (Or.inl rfl))
  obtain ⟨c', hC', hmC'⟩ := helper _ _ (htrans 3 (by decide) 3 (Or.inr rfl))
  exact checkSources_sound _ _ _ _ h
    _ (signature_mem hσ hr hsm) _ hmT _ hmA _ hmA' _ hmB _ hmB' _ hmC _ hmC'
    (actual_joined (hS.trans hv.symm) hT hA hA' hB hB' hC hC')

/-- Coverage of a family of checked source blocks suffices for the full theorem.
Each block ranges all atlas representatives for the non-source bands. -/
theorem exclude_of_checked_blocks (atlas : AtlasComplete)
    (σ : Bitsets.Cube → CutRow) (hσ : ∀ w, σ w = cutsOf w)
    (blocks : Array Block) (h : ∀ b ∈ blocks, checkBlock σ b = true)
    (cover : ∀ r ∈ atlasPlanes, ∃ b ∈ blocks, r ∈ b.sources ∧ (∀ w ∈ atlasPlanes, w ∈ b.domain))
    (C : Finset (Tuple 4)) (hc : packing cycleStep C) :
    ¬ ∀ k, ∃ i ∈ fullStarts C k, i+3 ∈ fullStarts C k := by
  intro ht
  obtain ⟨D, hd, hf, r, v, hs⟩ := normalize atlas hc ht
  obtain ⟨b, hb, hr, hdom⟩ := cover _ (Array.getElem_mem r.isLt)
  have orb (k : Fin 4) (t : ZMod 7) (ht : t ∈ fullStarts D k) :
      InOrbit b.domain (projectedBand D k t) := by
    obtain ⟨inj, hcode⟩ := Bands.band_projection hd k t
    have he : (projectedBand D k t).card = 33 :=
      (Finset.card_image_iff.mpr inj).trans (Finset.mem_filter.mp ht).2
    obtain ⟨r', g, e⟩ := atlas _ hcode he
    exact ⟨_, hdom _ (Array.getElem_mem r'.isLt), g, e⟩
  apply checkBlock_sound σ hσ b (h b hb) D ⟨_, hr, v, hs⟩ (orb 0 3 (hf 0).2)
  intro k _ t h
  rcases h with rfl | rfl
  · exact orb k 0 (hf k).1
  · exact orb k 3 (hf k).2

end SevenCycle.TypeThree
