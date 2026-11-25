import SevenCycle.Atlas.Chain
import SevenCycle.Atlas.StrongPrefix
import SevenCycleRuntime.AtlasPrune

namespace SevenCycle.Atlas.CubePlanes

open Proof Blueprint Bitsets

private theorem prefix_mem_iff (C : Finset (Tuple 3)) (n : Nat) (x : Tuple 3) :
    x ∈ cubeSet (prefixCube (initialPlanes C n)) ↔ x ∈ C ∧ (x 0).val < n := by
  rw [mem_cubeSet]
  change planeMem ((prefixCube (initialPlanes C n))[(x 0).val]'(x 0).isLt) (Fin.tail x) ↔ _
  simp only [prefixCube, Vector.getElem_ofFn]
  by_cases hi : (x 0).val < n
  · have h : (x 0).val < (initialPlanes C n).size := by simpa using hi
    rw [Array.getElem?_eq_getElem h, Option.getD_some, initialPlanes_get]
    rw [ZMod.natCast_zmod_val, ← mem_planeSet, mem_plane, Fin.cons_self_tail]
    simp [hi]
  · rw [Array.getElem?_eq_none (by simp; omega), Option.getD_none]
    simp [hi, planeMem]

private theorem prefixCut_eq (C : Finset (Tuple 3)) (j : Fin 7) (k : Fin 3) (hk : k ≠ 0) (s : ZMod 7) :
    planeSet (TypeThree.fastCut (prefixCube (initialPlanes C (j.val+1))) k s) =
      (projectedBand C k s).filter (fun y => (y 0).val ≤ j.val) := by
  rw [TypeThree.fastCut_eq, planeSet_cut]
  have axis : ∀ i : Fin 3, i ≠ 0 → i.succAbove 0 = 0 := by decide
  have hfirst (x : Tuple 3) : (dropCoord k x) 0 = x 0 := by simp [dropCoord, axis k hk]
  change ((cubeSet (prefixCube (initialPlanes C (j.val+1)))).filter
      (fun x => x k = s ∨ x k = s+1)).image (dropCoord k) = _
  ext y
  simp only [projectedBand, band, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨hx,hband⟩,rfl⟩
    obtain ⟨hc,hj⟩ := (prefix_mem_iff C (j.val+1) x).mp hx
    exact ⟨⟨x,⟨hc,hband⟩,rfl⟩, by rw [hfirst]; omega⟩
  · rintro ⟨⟨x,⟨hx,hband⟩,rfl⟩,hj⟩
    rw [hfirst] at hj
    exact ⟨x,⟨(prefix_mem_iff C (j.val+1) x).mpr ⟨hx,by omega⟩,hband⟩,rfl⟩

/-- j planes have been stored. The bound is evaluated at the last stored height. -/
def strongPrune (budget j : Nat) (stack : Array Plane) : Bool :=
  if h : 0 < j ∧ j < 7 then
    SevenCycleRuntime.AtlasPrune.check Completions.fullTable WindowDP.completionBounds budget ⟨j-1, by omega⟩ stack
  else true

theorem strongPrune_sound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hc : packing cycleStep C) {budget : Nat} (hb : 70 ≤ 2*C.card + budget)
    (j : Nat) : strongPrune budget j (initialPlanes C j) = true := by
  unfold strongPrune
  split
  · rename_i hj
    change strongPrefix budget ⟨j-1, by omega⟩ (initialPlanes C j) = true
    apply strongPrefix_sound hplan hc hb
    intro k hk s
    have e := prefixCut_eq C ⟨j-1, by omega⟩ k hk s
    simpa only [show j-1+1 = j by omega] using e
  · rfl

end SevenCycle.Atlas.CubePlanes
