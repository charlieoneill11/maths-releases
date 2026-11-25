import SevenCycle.Atlas.Completions
import SevenCycle.Atlas.CubePlanes
import SevenCycle.TypeThree.FastCuts

/-! A transverse band already inconsistent with all planar maxima costs
at least one unit of the cube code's deficit, even on a partial plane chain. -/

namespace SevenCycle.Atlas.CubePlanes

open Proof Blueprint Bitsets Completions

/-- Unchosen planes in a chain prefix are empty. -/
def prefixCube (planes : Array Plane) : Cube :=
  Vector.ofFn fun i => planes[i.val]?.getD 0

/-- If every stored plane lies in its actual level, filling the tail with
zero planes yields a subset of the original code. -/
theorem prefixCube_subset {C : Finset (Tuple 3)} {planes : Array Plane}
    (h : ∀ i : Fin 7, ∀ hi : i.val < planes.size, planeSet planes[i.val] ⊆ planeSet (plane C i)) :
    cubeSet (prefixCube planes) ⊆ C := by
  intro x hx
  have hbit : planeMem (planes[(x 0).val]?.getD 0) (Fin.tail x) := by
    have bit := (mem_cubeSet _ _).mp hx
    change ((prefixCube planes)[(x 0).val]'(x 0).isLt).toNat.testBit (index (Fin.tail x)) = true at bit
    simpa only [prefixCube, Vector.getElem_ofFn] using bit
  by_cases hi : (x 0).val < planes.size
  · rw [Array.getElem?_eq_getElem hi] at hbit
    have hy := h (x 0) hi ((mem_planeSet ..).mpr hbit)
    simpa only [Fin.cons_self_tail] using (mem_plane C _ _).mp hy
  · simp [Array.getElem?_eq_none (by omega : planes.size ≤ (x 0).val), planeMem] at hbit

private def missing (c : Cube) (k : Fin 3) (s : ZMod 7) : Nat :=
  if fullTable.contains (TypeThree.fastCut c k s) then 0 else 1

/-- The seven starts are unrolled for the compiled search. -/
@[inline] private def misses (c : Cube) (k : Fin 3) : Nat :=
  let f := missing c k
  f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + f 6)))))

def prefixOK (budget : Nat) (planes : Array Plane) : Bool :=
  let c := prefixCube planes
  decide (misses c 1 ≤ budget) && decide (misses c 2 ≤ budget)

private theorem misses_eq (c : Cube) (k : Fin 3) :
    misses c k = ∑ i : ZMod 7, missing c k i := by
  rw [Deficits.sum_seven_at _ 0]
  simp [misses]

/-- A full projected band of the eventual code is itself a table entry
containing the corresponding projection of the prefix. -/
private theorem missing_bound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hC : packing cycleStep C) {c : Cube} (hsub : cubeSet c ⊆ C)
    (k : Fin 3) (s : ZMod 7) : missing c k s + (band C k s).card ≤ 10 := by
  have hle : (band C k s).card ≤ 10 := Bands.band_card_le card_le_ten C hC k s
  by_cases hfull : (band C k s).card = 10
  · obtain ⟨inj, hc⟩ := Bands.band_projection hC k s
    have hcard : (projectedBand C k s).card = 10 := (Finset.card_image_iff.mpr inj).trans hfull
    obtain ⟨m, hm, hmask⟩ := Planar.maxMasks_complete hplan _ hc hcard
    have sub : planeSet (Bitsets.cut c k s) ⊆ planeSet m := by
      rw [planeSet_cut, hmask]
      apply Finset.image_mono
      exact Finset.filter_subset_filter _ hsub
    have hit := fullTable_contains m _ hm (canonical_cut c k s) sub
    simp [missing, TypeThree.fastCut_eq, hit, hfull]
  · unfold missing
    split <;> omega

theorem prefixOK_sound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hC : packing cycleStep C) {planes : Array Plane}
    (hsub : cubeSet (prefixCube planes) ⊆ C) {budget : Nat} (hbudget : 70 ≤ 2*C.card + budget) :
    prefixOK budget planes = true := by
  have axis (k : Fin 3) : misses (prefixCube planes) k ≤ budget := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => missing_bound hplan hC hsub k i)
    have hb : ∑ i : ZMod 7, (band C k i).card = 2*C.card := Bands.sum_band_card C k
    rw [Finset.sum_add_distrib, hb] at hsum
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hsum
    rw [misses_eq]
    omega
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (axis 1), decide_eq_true (axis 2)⟩

end SevenCycle.Atlas.CubePlanes
