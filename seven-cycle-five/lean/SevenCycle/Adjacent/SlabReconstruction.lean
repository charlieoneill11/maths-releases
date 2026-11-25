import SevenCycleRuntime.SlabReconstruction
import SevenCycle.Adjacent.FrameGeometry
import SevenCycle.Adjacent.Sites
import SevenCycle.Proof.Crossings

namespace SevenCycle.Adjacent.SlabReconstruction

open Blueprint Proof SlabJoin Bitsets

def center (cs : Centers) (x : Tuple 4) : Tuple 4 :=
  fun i => x i - Fin.cons (α := fun _ => ZMod 7) 1 (fun a => cs.get a) i

def sourceTail (cs : Centers) (x : Tuple 4) : Tuple 3 :=
  fun i => x i.succ + (show ZMod 7 from cs.get i)

def normSlab (C : Finset (Tuple 4)) : Finset (Tuple 4) := level C 0 0 ∪ level C 0 1 ∪ level C 0 2

private theorem centeredLevel (cs : Centers) (p : Finset (Tuple 3)) (h : ZMod 7) (x : Tuple 4) :
    x ∈ (p.image (Fin.cons (α := fun _ => ZMod 7) h)).image (center cs) ↔
      x 0 = h-1 ∧ sourceTail cs x ∈ p := by
  constructor
  · rintro hx
    obtain ⟨_,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨by simp [center],?_⟩
    have eq : sourceTail cs (center cs (Fin.cons h w)) = w := by
      funext j
      simp [center,sourceTail]
    rwa [eq]
  · rintro ⟨hh,hw⟩
    refine Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨_,hw,rfl⟩,?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [center] using hh.symm
    · simp [center,sourceTail]

private theorem physical_iff (C : Finset (Tuple 4)) (code : packing cycleStep C)
    (s t u : Bitsets.Cube) (hs : cubeSet s = projectedBand C 0 0)
    (ht : cubeSet t = projectedBand C 0 1) (hu : cubeSet u = projectedLevel C 0 1)
    (cs : Centers) (x : Tuple 4) : x ∈ (normSlab C).image (center cs) ↔
      (x 0 = 6 ∧ sourceTail cs x ∈ cubeSet s ∧ sourceTail cs x ∉ cubeSet u) ∨
      (x 0 = 0 ∧ sourceTail cs x ∈ cubeSet u) ∨
      (x 0 = 1 ∧ sourceTail cs x ∈ cubeSet t ∧ sourceTail cs x ∉ cubeSet u) := by
  obtain ⟨_, ha, hb, hc⟩ := Crossings.slabs C code 0 1
  simp only [sub_self, one_add_one_eq_two, Fin.insertNth_zero'] at ha hb hc
  rw [normSlab,ha,hb,hc,← hs,← ht,← hu,Finset.image_union,Finset.image_union]
  simp only [Finset.mem_union,centeredLevel,Finset.mem_sdiff]
  rw [show (0:ZMod 7)-1 = 6 by decide,show (1:ZMod 7)-1 = 0 by decide,
    show (2:ZMod 7)-1 = 1 by decide]
  tauto

private theorem source_eq (cs : Centers) (i : Fin 2401) :
    (sourceSite cs i.val).word = sourceTail cs (position i.val) := by
  have digit (k : Fin 4) : Fin.ofNat 7 (coords i.val k) = position i.val k := by
    rw [coords_position i k]
    exact Fin.ext (Nat.mod_eq_of_lt (ZMod.val_lt _))
  funext k
  fin_cases k
  · change Fin.ofNat 7 (coords i.val 1) + cs.get 0 = _
    rw [digit]
    rfl
  · change Fin.ofNat 7 (coords i.val 2) + cs.get 1 = _
    rw [digit]
    rfl
  · change Fin.ofNat 7 (coords i.val 3) + cs.get 2 = _
    rw [digit]
    rfl

theorem centeredMask_stores (C : Finset (Tuple 4)) (code : packing cycleStep C)
    (s t u : Bitsets.Cube) (hs : cubeSet s = projectedBand C 0 0)
    (ht : cubeSet t = projectedBand C 0 1) (hu : cubeSet u = projectedLevel C 0 1)
    (cs : Centers) : Stores (centeredMask s t u cs) ((normSlab C).image (center cs)) := by
  have height : ∀ (h : ZMod 7) (a b c : Bool),
      (if h.val == 6 then a && !c else if h.val == 0 then c else if h.val == 1 then b && !c else false) = true ↔
        (h = 6 ∧ a = true ∧ c ≠ true) ∨ (h = 0 ∧ c = true) ∨ (h = 1 ∧ b = true ∧ c ≠ true) := by decide
  intro j
  rw [centeredMask,maskUpTo_bit,Bool.and_eq_true_iff,decide_eq_true_eq]
  apply and_congr_right
  intro hj
  rw [occupiedAt, coords_position ⟨j,hj⟩ 0, height,physical_iff C code s t u hs ht hu]
  have un : Middle.occupied u (sourceSite cs j) ≠ true ↔ sourceTail cs (position j) ∉ cubeSet u := by
    apply not_congr
    rw [Middle.occupied_iff, source_eq cs ⟨j,hj⟩]
  simp only [un, Middle.occupied_iff,source_eq cs ⟨j,hj⟩]

private theorem identity_image (r : String) :
    ((rowPoints r).image (signedAction identityOrder 0)) = rowPoints r := by
  have eq : signedAction identityOrder 0 = id := by
    funext x i; fin_cases i <;> rfl
  rw [eq, Finset.image_id]

theorem recorded_sound (rows : Array String) (C : Finset (Tuple 4)) (code : packing cycleStep C)
    (s t u : Bitsets.Cube) (hs : cubeSet s = projectedBand C 0 0)
    (ht : cubeSet t = projectedBand C 0 1) (hu : cubeSet u = projectedLevel C 0 1)
    (cs : Centers) (h : recorded (rowIndex rows) s t cs u = true) :
    ∃ r ∈ rows, (normSlab C).image (center cs) = rowPoints r := by
  simp only [recorded,rowIndex,Std.HashSet.ofArray_eq_ofList,Std.HashSet.contains_ofList,
    List.contains_iff_mem,Array.mem_toList_iff,Array.mem_map] at h
  obtain ⟨r,hr,eq⟩ := h
  have hst := moved_stores r identityOrder 0
  have eb : movedMask (oneBitMap identityOrder 0) (readSlab r) = centeredMask s t u cs := congrArg FrameMask.bits eq
  rw [identity_image, eb] at hst
  have ref := centeredMask_stores C code s t u hs ht hu cs
  refine ⟨r,hr,?_⟩
  ext x
  obtain ⟨hj,e⟩ := UnionMasks.components x
  simpa only [e,hj,true_and] using (ref (address x)).symm.trans (hst (address x))

end SevenCycle.Adjacent.SlabReconstruction
