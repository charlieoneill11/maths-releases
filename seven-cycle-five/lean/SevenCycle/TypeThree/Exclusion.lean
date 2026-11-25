import SevenCycle.TypeThree.Normalize
import SevenCycle.Bitsets.Orbit

/-! # Sufficiency of a checked search over the labelled atlas

Coverage refers to individual rows after decoding; duplicate images are
harmless. The theorem takes the two independent obligations explicitly:
completeness of the atlas and exclusion of joins among the enumerated rows. -/

namespace SevenCycle.TypeThree
open SevenCycle.Proof SevenCycle.Blueprint

def CoversImages (rows : Array CutRow) (images : Bitsets.Cube → Array Bitsets.Cube) : Prop :=
  ∀ r : Fin atlasPlanes.size, ∀ w ∈ images atlasPlanes[r], cutsOf w ∈ rows

def collectRows (images : Bitsets.Cube → Array Bitsets.Cube)
    (signature : Bitsets.Cube → CutRow) : Array CutRow :=
  atlasPlanes.flatMap fun r => (images r).map signature

theorem covers_collectRows (images : Bitsets.Cube → Array Bitsets.Cube)
    (signature : Bitsets.Cube → CutRow) (h : ∀ w, signature w = cutsOf w) :
    CoversImages (collectRows images signature) images := by
  intro r w hw
  exact Array.mem_flatMap.mpr ⟨_, Array.getElem_mem r.isLt,
    Array.mem_map.mpr ⟨w, hw, h w⟩⟩

private theorem full_row (atlas : AtlasComplete) {D : Finset (Tuple 4)}
    (hd : packing cycleStep D) (k : Fin 4) (h : ZMod 7) (hf : h ∈ fullStarts D k)
    (rows : Array CutRow) (covers : CoversImages rows Bitsets.orbitImages) :
    ∃ w, RepresentsBand D k h w ∧ cutsOf w ∈ rows := by
  obtain ⟨hinj, hcode⟩ := Bands.band_projection hd k h
  have hsize : (projectedBand D k h).card = 33 :=
    (Finset.card_image_iff.mpr hinj).trans (Finset.mem_filter.mp hf).2
  obtain ⟨r, g, hg⟩ := atlas _ hcode hsize
  obtain ⟨w, hw, hrep⟩ := Bitsets.orbitImages_complete g atlasPlanes[r]
  exact ⟨w, hrep.trans hg.symm, covers r w hw⟩

/-- Proposition 17 follows from coverage of both concrete tables and exhaustion
of the search on those tables. There is no assumption on the size of C. -/
theorem exclude_of_noJoined (atlas : AtlasComplete) {sources rows : Array CutRow}
    (hsources : CoversImages sources Bitsets.translationImages)
    (hrows : CoversImages rows Bitsets.orbitImages) (he : NoJoined sources rows)
    (C : Finset (Tuple 4)) (hC : packing cycleStep C) :
    ¬ ∀ k, ∃ i ∈ fullStarts C k, i+3 ∈ fullStarts C k := by
  intro h
  obtain ⟨D, hd, hf, r, v, hs⟩ := normalize atlas hC h
  obtain ⟨s, hsmem, hsrep⟩ := Bitsets.translationImages_complete v atlasPlanes[r]
  have hS : RepresentsBand D 0 0 s := hsrep.trans hs.symm
  obtain ⟨t, hT, ht⟩ := full_row atlas hd 0 3 (hf 0).2 rows hrows
  obtain ⟨a, hA, ha⟩ := full_row atlas hd 1 0 (hf 1).1 rows hrows
  obtain ⟨a', hA', ha'⟩ := full_row atlas hd 1 3 (hf 1).2 rows hrows
  obtain ⟨b, hB, hb⟩ := full_row atlas hd 2 0 (hf 2).1 rows hrows
  obtain ⟨b', hB', hb'⟩ := full_row atlas hd 2 3 (hf 2).2 rows hrows
  obtain ⟨c, hC', hc⟩ := full_row atlas hd 3 0 (hf 3).1 rows hrows
  obtain ⟨c', hC'', hc'⟩ := full_row atlas hd 3 3 (hf 3).2 rows hrows
  exact he _ (hsources r s hsmem) _ ht _ ha _ ha' _ hb _ hb' _ hc _ hc'
    (actual_joined hS hT hA hA' hB hB' hC' hC'')

end SevenCycle.TypeThree
