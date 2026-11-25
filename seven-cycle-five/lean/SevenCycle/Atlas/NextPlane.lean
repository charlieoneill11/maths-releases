import SevenCycle.Atlas.MaskSearch
import SevenCycle.Atlas.Completions

/-! # Coverage of one step of the normalized plane-chain search -/

namespace SevenCycle.Atlas.CubePlanes

open Proof Blueprint Bitsets

/-- Complementary half of a full band whose first half is p. -/
def otherHalf (m p : Plane) := m &&& (m ^^^ p)

theorem otherHalf_eq {m p q : Plane} (hm : Canonical m) (hq : Canonical q)
    (h : planeSet m = planeSet p ∪ planeSet q) (hdisj : Disjoint (planeSet p) (planeSet q)) :
    otherHalf m p = q := by
  have hcan : Canonical (otherHalf m p) := by intro i hi; simp [otherHalf, hm i hi]
  apply plane_eq_of_set_eq hcan hq
  ext x
  simp only [otherHalf, mem_planeSet, planeMem, UInt64.toNat_and, Nat.testBit_and,
    UInt64.toNat_xor, Nat.testBit_xor]
  have hm' := Finset.ext_iff.mp h x
  simp only [mem_planeSet, planeMem, Finset.mem_union] at hm'
  have hd' : x ∈ planeSet p → x ∉ planeSet q := fun hx => Finset.disjoint_left.mp hdisj hx
  simp only [mem_planeSet, planeMem] at hd'
  cases hmp : m.toNat.testBit (index x) <;>
    cases hpp : p.toNat.testBit (index x) <;> cases hqp : q.toNat.testBit (index x) <;> simp_all

theorem plane_parts (C : Finset (Tuple 3)) (j : ZMod 7) : projectedBand C 0 j = planeSet (plane C j) ∪ planeSet (plane C (j+1)) := by
  ext y
  simp only [projectedBand, band, Finset.mem_image, Finset.mem_filter, Finset.mem_union, mem_plane]
  constructor
  · rintro ⟨x, ⟨hx, hj⟩, hy⟩
    have ht : Fin.tail x = y := by simpa [dropCoord, Fin.tail] using hy
    rcases hj with hj | hj
    · left; simpa [← hj, ← ht] using hx
    · right; simpa [← hj, ← ht] using hx
  · rintro (hy | hy)
    · exact ⟨_, ⟨hy, Or.inl rfl⟩, by funext k; simp [Blueprint.dropCoord, Fin.zero_succAbove]⟩
    · exact ⟨_, ⟨hy, Or.inr rfl⟩, by funext k; simp [Blueprint.dropCoord, Fin.zero_succAbove]⟩

/-- Extend a fixed preceding plane. At a full window consult the complete
index of ten-sets, otherwise enumerate all compatible independent planes. -/
def visitNext (p : Plane) (need : Nat) (full : Bool) (visit : Plane → Bool) : Bool :=
  if full then
    (Completions.fullTable.getD p #[]).all fun m => visit (otherHalf m p)
  else MaskSearch.visitNew p need visit

theorem visitNext_sound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hc : packing cycleStep C) (j : ZMod 7) (need : Nat)
    (hsize : planeCard (plane C (j+1)) = need) (full : Bool)
    (hfull : full = true → (band C 0 j).card = 10)
    (visit : Plane → Bool) (h : visitNext (plane C j) need full visit = true) :
    visit (plane C (j+1)) = true := by
  have hq (s : ZMod 7) : Canonical (plane C s) := canonical_buildPlane _
  have hcomp := adjacent_compatible hc j
  cases full with
  | false =>
    apply MaskSearch.visitNew_sound (hq _) (plane_code hc _) _ need hsize visit h
    apply (compatible_iff ..).mpr
    intro y hy x hx hnear
    apply (compatible_iff ..).mp hcomp x hx y hy
    intro i
    have sym : ∀ a b : ZMod 7, cycleStep a b → cycleStep b a := by unfold cycleStep; decide
    exact sym _ _ (hnear i)
  | true =>
    have hparts := plane_parts C j
    obtain ⟨hinj,hcode⟩ := Bands.band_projection hc 0 j
    obtain ⟨m, hm, he⟩ := Planar.maxMasks_complete hplan _ hcode
      ((Finset.card_image_iff.mpr hinj).trans (hfull rfl))
    change planeSet m = projectedBand C 0 j at he
    have covers := he.trans hparts
    have hlookup := Completions.fullTable_covers m (plane C j) hm (hq _) (by rw [covers]; exact Finset.subset_union_left)
    have hd : Disjoint (planeSet (plane C j)) (planeSet (plane C (j+1))) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (compatible_iff ..).mp hcomp x hx x hy (fun _ => by simp [cycleStep])
    have heq := otherHalf_eq (Planar.maxMasks_canonical hm) (hq _) covers hd
    simpa only [heq] using Array.all_eq_true'.mp h m hlookup

end SevenCycle.Atlas.CubePlanes
