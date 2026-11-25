import SevenCycleRuntime.MixedSlabs
import SevenCycle.Adjacent.FrameGeometry

namespace SevenCycle.Adjacent.MixedSlabs

open Proof Blueprint SlabJoin

def action (p : Profile) (o : AxisOrder) (s : Nat) (x : Tuple 4) : Tuple 4 := fun k =>
  if s.testBit k.val then 1 - (show ZMod 7 from p.get k) - x o[k] else x o[k]

private theorem site_address (p : Profile) (o : AxisOrder) (s : Nat) (j : Fin 2401) :
    imageSite p o s j.val = address (action p o s (position j.val)) := by
  have table : ∀ (x d : ZMod 7), (1-d-x).val = (15-d.val-x.val)%7 := by decide
  have atAxis (k : Fin 4) :
      (if s.testBit k.val then (15 - (p.get k).val - coords j.val o[k]) % 7 else coords j.val o[k]) =
        (action p o s (position j.val) k).val := by
    rw [coords_position j o[k]]
    unfold action
    split
    · exact (table _ _).symm
    · rfl
  simp only [imageSite,address,atAxis]

theorem stores_mask (r : String) (p : Profile) (o : AxisOrder) (s : Nat) :
    Stores (movedMask (addressMap p o s) (readSlab r)) ((rowPoints r).image (action p o s)) := by
  apply addressMap_stores r _ _ (by simp [addressMap])
  intro i hi
  simp [addressMap,hi,site_address p o s ⟨i,hi⟩]

theorem transform_mem (p : Profile) (k : Fin 4) (o : AxisOrder) (s : Fin 16)
    (inj : Function.Injective (fun j : Fin 4 => o[j])) (h : o[k] = 0)
    (pres : ∀ j : Fin 4, p.get j = p.get o[j]) (first : k = 0 → o = identityOrder ∧ s.val = 0) :
    (o,s.val) ∈ transforms p k := by
  by_cases eq : k = 0
  · obtain ⟨rfl,hs⟩ := first eq
    simp [transforms,eq,hs]
  · have ok : sameProfile p o = true :=
      Array.all_eq_true_iff_forall_mem.mpr fun j _ => beq_iff_eq.mpr (pres j)
    simp only [transforms,eq,if_false,Array.mem_flatMap,Array.mem_filter,Array.mem_map]
    exact ⟨o,⟨orders_complete o inj, by simp [h,ok]⟩,s.val, by simp [s.isLt],rfl⟩

/-- Exact physical coverage by one transformed source slab. -/
def Covers (p : Profile) (rows : Array String) (k : Fin 4) (A : Finset (Tuple 4)) : Prop :=
  ∃ row ∈ rows, ∃ m ∈ transforms p k, A = (rowPoints row).image (action p m.1 m.2)

theorem of_cover {p : Profile} {rows : Array String} {k : Fin 4} {A : Finset (Tuple 4)}
    (cover : Covers p rows k A) : ∃ n, Stores n A ∧ ofBits n ∈ domain (rows.map readSlab) p k := by
  obtain ⟨r,hr,⟨o,s⟩,hm,rfl⟩ := cover
  let n := movedMask (addressMap p o s) (readSlab r)
  refine ⟨n,stores_mask r p o s,?_⟩
  apply Array.mem_map.mpr
  refine ⟨⟨n⟩,?_,cached_eq n⟩
  rw [Std.HashSet.mem_toArray,Std.HashSet.ofArray_eq_ofList,Std.HashSet.mem_ofList,List.contains_iff_mem,Array.mem_toList_iff]
  exact Array.mem_flatMap.mpr ⟨(o,s),hm,Array.mem_map.mpr ⟨readSlab r,Array.mem_map_of_mem hr,rfl⟩⟩

attribute [local irreducible] blocksFrom neighborTable

private theorem actual_fits {C : Finset (Tuple 4)} (hc : packing cycleStep C)
    (a b : Fin 4) {s t : Nat} (hs : Stores s (C.filter (inThree a)))
    (ht : Stores t (C.filter (inThree b))) :
    fits (active neighborTable (ofBits s)) (active neighborTable (ofBits t)) a b = true := by
  have face (n : Nat) (k : Fin 4) : faceKey (ofBits n) k = key n k := by fin_cases k <;> rfl
  exact Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr ((face s b).trans ((keys_agree hs ht).trans (face t a).symm)),
    beq_iff_eq.mpr (clear_of_code hc ht hs)⟩

theorem two_sound (C : Finset (Tuple 4)) (hc : packing cycleStep C) (p : Profile)
    (rows : Array String) (leaf : Nat → Bool) (arity : p.get 2 ≠ 1)
    (ca : Covers p rows 0 (C.filter (inThree 0))) (cb : Covers p rows 1 (C.filter (inThree 1)))
    (ok : check p rows leaf = true) :
    ∃ s t, Stores s (C.filter (inThree 0)) ∧ Stores t (C.filter (inThree 1)) ∧ leaf (s ||| t) = true := by
  obtain ⟨s,hs,mems⟩ := of_cover ca
  obtain ⟨t,ht,memt⟩ := of_cover cb
  have get := Array.all_eq_true'.mp (Array.all_eq_true'.mp ok _ (Array.mem_map_of_mem mems)) _ (Array.mem_map_of_mem memt)
  simp only [actual_fits hc _ _ hs ht, Bool.not_true, Bool.false_or, beq_iff_eq, if_neg arity] at get
  exact ⟨s,t,hs,ht,get⟩

theorem three_sound (C : Finset (Tuple 4)) (hc : packing cycleStep C) (p : Profile)
    (rows : Array String) (leaf : Nat → Bool) (arity : p.get 2 = 1)
    (ca : Covers p rows 0 (C.filter (inThree 0))) (cb : Covers p rows 1 (C.filter (inThree 1)))
    (cc : Covers p rows 2 (C.filter (inThree 2))) (ok : check p rows leaf = true) :
    ∃ s t u, Stores s (C.filter (inThree 0)) ∧ Stores t (C.filter (inThree 1)) ∧
      Stores u (C.filter (inThree 2)) ∧ leaf (s ||| t ||| u) = true := by
  obtain ⟨s,hs,mems⟩ := of_cover ca
  obtain ⟨t,ht,memt⟩ := of_cover cb
  obtain ⟨u,hu,memu⟩ := of_cover cc
  have get := Array.all_eq_true'.mp (Array.all_eq_true'.mp ok _ (Array.mem_map_of_mem mems)) _ (Array.mem_map_of_mem memt)
  simp only [actual_fits hc _ _ hs ht, Bool.not_true, Bool.false_or, arity, beq_self_eq_true, if_true] at get
  have last := Array.all_eq_true'.mp get _ (Array.mem_map_of_mem memu)
  simp only [actual_fits hc _ _ hs hu, actual_fits hc _ _ ht hu, Bool.and_self, Bool.not_true,Bool.false_or] at last
  exact ⟨s,t,u,hs,ht,hu,last⟩

end SevenCycle.Adjacent.MixedSlabs
