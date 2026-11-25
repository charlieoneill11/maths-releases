import SevenCycle.Adjacent.Support
import SevenCycle.Bitsets.Orbit
import SevenCycle.TypeThree.Normalize

namespace SevenCycle.Adjacent

open Proof Blueprint Bitsets

def unpack (c : SupportCube) : Cube := #v[c.h0,c.h1,c.h2,c.h3,c.h4,c.h5,c.h6]

theorem unpack_pack (c : Cube) : unpack (pack c) = c := by
  apply Vector.ext
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The orbit generator runs once per target class. Every atlas row occurs
in the distinguished support position. The target class array can be a chunk. -/
def checkSupportClasses (classes : Array Cube) (next : Cube → Cube → Bool) : Bool :=
  let anchors := atlasPlanes.map pack
  classes.all fun c =>
    checkSupports anchors ((orbitImages c).map pack) (fun s t => next (unpack s) (unpack t))

theorem checkSupportClasses_retains (classes : Array Cube) (next : Cube → Cube → Bool)
    (ok : checkSupportClasses classes next = true) (a : Fin atlasPlanes.size)
    {c t : Cube} (hc : c ∈ classes) (ht : t ∈ orbitImages c)
    {u : Finset (Tuple 3)} (hsub : u ⊆ cubeSet atlasPlanes[a] ∩ cubeSet t)
    (hu : 16 ≤ u.card) : next atlasPlanes[a] t = true := by
  have yes := Array.all_eq_true_iff_forall_mem.mp ok c hc
  have h := checkSupports_sound yes (Array.mem_map_of_mem (Array.getElem_mem a.isLt))
    (Array.mem_map_of_mem ht) hsub hu
  simpa only [unpack_pack] using h

/-- Normalize a chosen marked centre with Lemma 11. The projected middle layer
survives the support test against a genuine generated relative image. -/
theorem normalized_support_frame (atlas : TypeThree.AtlasComplete) {C : Finset (Tuple 4)}
    (code : packing cycleStep C) (k : Fin 4) (c : ZMod 7) (hc : HasCentre C k c) :
    ∃ g : Blueprint.Isometry 4, ∃ a b : Fin atlasPlanes.size, ∃ t ∈ orbitImages atlasPlanes[b],
      (∀ x : Tuple 4, act g x 0 = x k - (c-1)) ∧
      packing cycleStep (actOnCode g C) ∧
      projectedBand (actOnCode g C) 0 0 = cubeSet atlasPlanes[a] ∧
      projectedBand (actOnCode g C) 0 1 = cubeSet t ∧
      projectedLevel (actOnCode g C) 0 1 ⊆ cubeSet atlasPlanes[a] ∩ cubeSet t ∧
      16 ≤ (projectedLevel (actOnCode g C) 0 1).card ∧
      (projectedLevel (actOnCode g C) 0 1).card ≤ 19 := by
  obtain ⟨g, _, hg, hcode, _, _, h1, a, ha⟩ :=
    Crossings.normalise_full_pair atlas C code k (c-1) 1 hc.1 (by simpa using hc.2.1)
  let D := actOnCode g C
  have hd : packing cycleStep D := hcode
  obtain ⟨hinj, hpack⟩ := Bands.band_projection hd 0 1
  have size : (projectedBand D 0 1).card = 33 :=
    (Finset.card_image_iff.mpr hinj).trans (Finset.mem_filter.mp h1).2
  obtain ⟨b, motion, moved⟩ := atlas _ hpack size
  obtain ⟨t,ht,et⟩ := orbitImages_complete motion atlasPlanes[b]
  have left : projectedBand D 0 0 = cubeSet atlasPlanes[a] := ha
  have right : projectedBand D 0 1 = cubeSet t := moved.trans et.symm
  have intersect : projectedLevel D 0 1 ⊆ cubeSet atlasPlanes[a] ∩ cubeSet t := by
    rw [← left, ← right]
    simpa using (Crossings.slabs D hd 0 1).1
  have height : ∀ (z w : ZMod 7), z - (w-1) = 1 ↔ z = w := by decide
  have levels : level D 0 1 = (level C k c).image (act g) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hD, hheight⟩ := Finset.mem_filter.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hD
      exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw,(height _ _).mp
        ((hg w).1.symm.trans hheight)⟩, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hw, eq⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,
        (hg w).1.trans ((height _ _).mpr eq)⟩
  have inj : Function.Injective (act g) := Function.LeftInverse.injective (f := act g) (g := act (Symmetry.undo g)) (Symmetry.undo_act g)
  have midcard : (projectedLevel D 0 1).card = (level C k c).card := by
    have sub : level D 0 1 ⊆ band D 0 1 := by
      intro w hw
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,Or.inl (Finset.mem_filter.mp hw).2⟩
    exact (Finset.card_image_iff.mpr (hinj.mono sub)).trans
      (levels ▸ Finset.card_image_of_injective _ inj)
  exact ⟨g,a,b,t,ht,fun x => (hg x).1,hd,left,right,intersect,midcard ▸ hc.2.2.1,midcard ▸ hc.2.2.2⟩

theorem normalized_support (atlas : TypeThree.AtlasComplete) {C : Finset (Tuple 4)}
    (code : packing cycleStep C) (k : Fin 4) (c : ZMod 7) (hc : HasCentre C k c) :
    ∃ g : Blueprint.Isometry 4, ∃ a b : Fin atlasPlanes.size, ∃ t ∈ orbitImages atlasPlanes[b],
      packing cycleStep (actOnCode g C) ∧
      projectedBand (actOnCode g C) 0 0 = cubeSet atlasPlanes[a] ∧
      projectedBand (actOnCode g C) 0 1 = cubeSet t ∧
      projectedLevel (actOnCode g C) 0 1 ⊆ cubeSet atlasPlanes[a] ∩ cubeSet t ∧
      16 ≤ (projectedLevel (actOnCode g C) 0 1).card ∧
      (projectedLevel (actOnCode g C) 0 1).card ≤ 19 := by
  obtain ⟨g,a,b,t,ht,_,rest⟩ := normalized_support_frame atlas code k c hc
  exact ⟨g,a,b,t,ht,rest⟩

/-- Any continuation certified on all target classes succeeds for the
configuration induced by an arbitrary actual marked 113-code. -/
theorem checked_normalized_support (atlas : TypeThree.AtlasComplete) {C : Finset (Tuple 4)}
    (code : packing cycleStep C) (k : Fin 4) (c : ZMod 7) (hc : HasCentre C k c)
    (next : Cube → Cube → Bool) (ok : checkSupportClasses atlasPlanes next = true) :
    ∃ g : Blueprint.Isometry 4, ∃ a : Fin atlasPlanes.size, ∃ t : Cube,
      projectedBand (actOnCode g C) 0 0 = cubeSet atlasPlanes[a] ∧
      projectedBand (actOnCode g C) 0 1 = cubeSet t ∧ next atlasPlanes[a] t = true := by
  obtain ⟨g,a,b,t,ht,_,ha,he,sub,lo,_⟩ := normalized_support atlas code k c hc
  exact ⟨g,a,t,ha,he,checkSupportClasses_retains atlasPlanes next ok a
    (Array.getElem_mem b.isLt) ht sub lo⟩

end SevenCycle.Adjacent
