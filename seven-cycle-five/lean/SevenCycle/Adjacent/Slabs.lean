import SevenCycle.Adjacent.Retention

namespace SevenCycle.Adjacent

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry

theorem lift_plane (C : Points) (k : Axis) (t : Height) :
    liftTo (plane C k t) k t = level C k t := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hk, rfl⟩ := mem_face.mp hy
    change z k = t at hk
    simp [setHeight, ← hk, level, hz, Function.update_eq_self]
  · intro hx
    obtain ⟨hxC, hkt⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_image.mpr ⟨setHeight x k 0, mem_face.mpr ⟨x, hxC, hkt, rfl⟩, ?_⟩
    simp [setHeight, ← hkt, Function.update_eq_self]

theorem slab_eq {C : Points} {m : Frame} {k : Axis} (hc : packing cycleStep C)
    (hk : m.gap k = 1) :
    slab m k (projections m C k false) (projections m C k true) (plane C k (start m k true)) =
      C.filter (inSlab m k) := by
  let a := m.base k
  have he : start m k true = a+1 := by simp [a, start, hk]
  unfold slab projections
  rw [show start m k false = a from rfl, he,
    ← plane_union C k a, ← plane_union C k (a+1),
    Finset.union_sdiff_cancel_right (planes_disjoint hc k a),
    Finset.union_sdiff_cancel_left (planes_disjoint hc k (a+1))]
  change liftTo (plane C k a) k a ∪ _ ∪ _ = _
  rw [lift_plane, lift_plane, lift_plane]
  ext x
  simp only [Finset.mem_union, level, Finset.mem_filter, inSlab, he, Finset.mem_insert,
    Finset.mem_singleton, a]
  tauto

private theorem erase_inSlab {m : Frame} {k l : Axis} (hl : l ≠ k) (x : Tuple 4) :
    inSlab m k (setHeight x l 0) ↔ inSlab m k x := by
  simp [inSlab, setHeight, Function.update_of_ne hl.symm]

theorem six_bands {C : Points} {m : Frame} {k : Axis} (hc : packing cycleStep C)
    (hm : Marked m C) (hk : m.gap k = 1) :
    AdjSixBand m k (projections m C k false) (projections m C k true)
      (plane C k (start m k true)) (projections m C) := by
  refine ⟨projected_join hc hm k, ?_, ?_⟩
  · intro l hl b
    exact face_comm C hl.symm (fun z => z = start m k true)
      (fun z => z = start m l b ∨ z = start m l b + 1)
  · intro l hl hgap
    unfold CentreCapacity
    rw [slab_eq hc hk]
    let c := start m l true
    let L := level C l c
    have hlo : 16 ≤ L.card := (hm.2.2 l hgap).2.2.1
    have partition := Finset.card_filter_add_card_filter_not (s := L) (inSlab m k)
    have inside : L.filter (inSlab m k) = (C.filter (inSlab m k)).filter (fun x => x l = c) := by
      ext x; simp [L, level, and_comm, and_left_comm]
    have inj : Set.InjOn (fun x => setHeight x l 0) ((L.filter (fun x => ¬inSlab m k x)) : Set _) := by
      intro x hx y hy he
      apply stripe_injective hc l c _ _ he
      · obtain ⟨hxC, hxc⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
        exact Finset.mem_filter.mpr ⟨hxC, Or.inl hxc⟩
      · obtain ⟨hyC, hyc⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hy).1
        exact Finset.mem_filter.mpr ⟨hyC, Or.inl hyc⟩
    have sub : ((L.filter (fun x => ¬inSlab m k x)).image fun x => setHeight x l 0) ⊆
        ((projections m C l false ∩ projections m C l true).filter fun x => ¬inSlab m k x) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxL, hout⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxC, hxc⟩ := Finset.mem_filter.mp hxL
      exact Finset.mem_filter.mpr ⟨middle_subset hgap (mem_face.mpr ⟨x, hxC, hxc, rfl⟩),
        fun h => hout ((erase_inSlab hl x).mp h)⟩
    have hout := Finset.card_le_card sub
    rw [Finset.card_image_of_injOn inj] at hout
    rw [← partition, inside] at hlo
    exact hlo.trans (Nat.add_le_add_left hout _)

theorem recorded {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C)
    {k : Axis} (hk : m.gap k = 1) : RecordedSlab m k (C.filter (inSlab m k)) := by
  exact ⟨_, _, _, _, support hc hm hk, contacts hc hm k, middle hc hm hk,
    six_bands hc hm hk, (slab_eq hc hk).symm⟩

theorem slab_union {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C) :
    AdjUnion m (C.filter (inUnion m)) := by
  refine ⟨fun k => C.filter (inSlab m k), fun _ hk => recorded hc hm hk, ?_, ?_, ?_⟩
  · intro k l _ _
    ext x
    simp [and_comm, and_left_comm]
  · intro x
    simp only [Finset.mem_filter, inUnion]
    constructor
    · rintro ⟨hx, k, hk, hi⟩
      exact ⟨k, hk, hx, hi⟩
    · rintro ⟨k, hk, hx, hi⟩
      exact ⟨hx, k, hk, hi⟩
  · exact fun x hx y hy => hc x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1

private theorem inUnion_erase {m : Frame} {k : Axis} (hk : m.gap k ≠ 1) (x : Tuple 4) :
    inUnion m (setHeight x k 0) ↔ inUnion m x := by
  constructor
  · rintro ⟨l, hl, hi⟩
    have hkl : k ≠ l := by rintro rfl; exact hk hl
    exact ⟨l, hl, (erase_inSlab hkl x).mp hi⟩
  · rintro ⟨l, hl, hi⟩
    have hkl : k ≠ l := by rintro rfl; exact hk hl
    exact ⟨l, hl, (erase_inSlab hkl x).mpr hi⟩

theorem remaining {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C) :
    Remaining m (C.filter (inUnion m)) (projections m C) := by
  refine ⟨fun k l _ _ h b c => stripe_comm C h _ _, ?_⟩
  intro k hk b
  refine ⟨face33 (k := k) (t := start m k b) hc (hm.2.1 k b), ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨hband, hreg⟩ := Finset.mem_filter.mp hy
      obtain ⟨x, hx, ht, rfl⟩ := mem_face.mp hband
      exact mem_face.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, (inUnion_erase hk x).mp hreg⟩, ht, rfl⟩
    · intro hy
      obtain ⟨x, hx, ht, rfl⟩ := mem_face.mp hy
      obtain ⟨hC, hreg⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨mem_face.mpr ⟨x, hC, ht, rfl⟩, (inUnion_erase hk x).mpr hreg⟩
  · intro y hy hout
    obtain ⟨x, hx, ht, rfl⟩ := mem_face.mp hy
    refine ⟨x k, ht, ?_⟩
    have e : setHeight (setHeight x k 0) k (x k) = x := by simp [setHeight, Function.update_eq_self]
    rw [e]
    exact ⟨fun h => hout ((inUnion_erase hk x).mpr (Finset.mem_filter.mp h).2),
      fun z hz => hc x hx z (Finset.mem_filter.mp hz).1⟩

end SevenCycle.Adjacent
