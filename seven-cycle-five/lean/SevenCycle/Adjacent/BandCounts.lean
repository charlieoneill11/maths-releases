import SevenCycleRuntime.BandCounts
import SevenCycle.Adjacent.Middle
import SevenCycle.Proof.Bands

namespace SevenCycle.Adjacent.BandCounts

open Blueprint Blueprint.SearchSpec Proof Bitsets

private theorem mask_mem : ∀ (a : Fin 3) (c i j k : Fin 7),
    (sliceMask a c)[i].toNat.testBit (7*j.val+k.val) = decide ((![i,j,k] : Tuple 3) a = c) := by
  decide +kernel

theorem sliceCount_eq (s : Cube) (a : Fin 3) (c : ZMod 7) :
    sliceCount s a c = ((cubeSet s).filter fun x => x a = c).card := by
  rw [sliceCount, Middle.count_eq]
  change (cubeSet (cubeInter s (sliceMask a c))).card = _
  rw [cubeSet_inter]
  congr 1
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter]
  apply and_congr_right
  intro _
  have e : (![x 0,x 1,x 2] : Tuple 3) = x := by funext i; fin_cases i <;> rfl
  rw [mem_cubeSet]
  let i : Fin 7 := x 0
  let j : Fin 7 := x 1
  let k : Fin 7 := x 2
  change (sliceMask a c)[i].toNat.testBit (7*j.val+k.val) = true ↔ x a = c
  rw [mask_mem a c i j k, decide_eq_true_eq]
  exact congrArg (fun w : Tuple 3 => w a = c) e |>.to_iff

theorem known_eq_of_slice (s t u v : Cube) (a : Fin 3) (c : ZMod 7)
    (h : ∀ x : Tuple 3, x a = c → (x ∈ cubeSet u ↔ x ∈ cubeSet v)) :
    known s t u a c = known s t v a c := by
  have e : (cubeSet u).filter (fun x => x a = c) = (cubeSet v).filter (fun x => x a = c) := by
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_left fun hc => h x hc
  simp only [known,sliceCount_eq,e]

private theorem count_projected (A : Points) (w : Cube)
    (hw : cubeSet w = A.image (dropCoord 0)) (hi : Set.InjOn (dropCoord 0) (A : Set (Tuple 4)))
    (a : Fin 3) (c : ZMod 7) :
    sliceCount w a c = (A.filter fun x => x a.succ = c).card := by
  rw [sliceCount_eq, hw, Finset.filter_image]
  exact Finset.card_image_of_injOn (hi.mono (Finset.filter_subset _ _))

theorem known_upper {C : Points} {m : Frame} {s t u : Cube}
    (hc : packing cycleStep C) (hb : m.base 0 = 0) (hg : m.gap 0 = 1)
    (hs : cubeSet s = projectedBand C 0 0) (ht : cubeSet t = projectedBand C 0 1)
    (hu : cubeSet u = projectedLevel C 0 1) (a : Fin 3) (c : ZMod 7) :
    ((C.filter (inSlab m 0)).filter (fun x => x a.succ = c)).card ≤ known s t u a c := by
  let L := C.filter fun x => x a.succ = c
  have bi (i : ZMod 7) : Set.InjOn (dropCoord 0) (band C 0 i : Set (Tuple 4)) :=
    (Bands.band_projection hc 0 i).1
  have li : Set.InjOn (dropCoord 0) (level C 0 1 : Set (Tuple 4)) := by
    apply (bi 1).mono
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, Or.inl (Finset.mem_filter.mp hx).2⟩
  have bc (w : Cube) (i : ZMod 7) (hw : cubeSet w = projectedBand C 0 i) :
      sliceCount w a c = (band L 0 i).card := by
    rw [count_projected _ _ hw (bi i)]
    congr 1
    exact Finset.filter_comm ..
  have lc : sliceCount u a c = (level L 0 1).card := by
    rw [count_projected _ _ hu li]
    congr 1
    exact Finset.filter_comm ..
  have union : (C.filter (inSlab m 0)).filter (fun x => x a.succ = c) =
      band L 0 0 ∪ band L 0 1 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, band, L, inSlab, start, hb, hg,
      ↓reduceIte, Nat.cast_one, zero_add, one_add_one_eq_two, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have inter : band L 0 0 ∩ band L 0 1 = level L 0 1 := by
    ext x
    simp only [Finset.mem_inter, band, level, Finset.mem_filter, zero_add, one_add_one_eq_two]
    constructor
    · rintro ⟨⟨hx,h | h⟩,⟨_,h' | h'⟩⟩
      · exact ⟨hx,h'⟩
      · exact False.elim ((by decide : (0 : ZMod 7) ≠ 2) (h.symm.trans h'))
      · exact ⟨hx,h⟩
      · exact ⟨hx,h⟩
    · rintro ⟨hx,h⟩
      exact ⟨⟨hx,Or.inr h⟩,hx,Or.inl h⟩
  rw [known,bc s 0 hs,bc t 1 ht,lc,union]
  have eq := Finset.card_union_add_card_inter (band L 0 0) (band L 0 1)
  rw [inter] at eq
  omega

end SevenCycle.Adjacent.BandCounts
