import SevenCycle.Proof.Frame

namespace SevenCycle.Adjacent

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry

theorem plane_sub_stripe {C : Points} {k : Axis} {s t : Height} (h : s = t ∨ s = t+1) :
    plane C k s ⊆ stripe C k t := by
  intro y hy
  obtain ⟨x, hx, hs, rfl⟩ := mem_face.mp hy
  exact mem_face.mpr ⟨x, hx, hs ▸ h, rfl⟩

theorem plane_card {C : Points} (hc : packing cycleStep C) (k : Axis) (t : Height) :
    (plane C k t).card = (level C k t).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  exact stripe_injective hc k t
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, Or.inl (Finset.mem_filter.mp ha).2⟩)
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, Or.inl (Finset.mem_filter.mp hb).2⟩) he

theorem middle_subset {C : Points} {m : Frame} {k : Axis} (hk : m.gap k = 1) :
    plane C k (start m k true) ⊆ projections m C k false ∩ projections m C k true := by
  exact Finset.subset_inter
    (plane_sub_stripe (Or.inr (by simp [start, hk])))
    (plane_sub_stripe (Or.inl rfl))

theorem support {C : Points} {m : Frame} {k : Axis} (hc : packing cycleStep C)
    (hm : Marked m C) (hk : m.gap k = 1) :
    AdjSupport k (projections m C k false) (projections m C k true) := by
  refine ⟨face33 (k := k) (t := start m k false) hc (hm.2.1 k false),
    face33 (k := k) (t := start m k true) hc (hm.2.1 k true), ?_⟩
  have hcard := (hm.2.2 k hk).2.2.1
  rw [← plane_card hc] at hcard
  exact hcard.trans (Finset.card_le_card (middle_subset hk))

theorem middle {C : Points} {m : Frame} {k : Axis} (hc : packing cycleStep C)
    (hm : Marked m C) (hk : m.gap k = 1) :
    AdjMiddle m k (projections m C k false) (projections m C k true)
      (plane C k (start m k true)) := by
  obtain ⟨_, _, hlo, hhi⟩ := hm.2.2 k hk
  refine ⟨middle_subset hk, (plane_card hc _ _).symm ▸ hlo, (plane_card hc _ _).symm ▸ hhi, ?_⟩
  intro l hl b
  refine ⟨projections m C l b, face33 (k := l) (t := start m l b) hc (hm.2.1 l b),
    ⟨stripe_comm C hl.symm _ _, stripe_comm C hl.symm _ _⟩, ?_⟩
  exact face_comm C hl.symm (fun z => z = start m k true)
    (fun z => z = start m l b ∨ z = start m l b + 1)

theorem exterior {C : Points} (hc : packing cycleStep C) (m : Frame) :
    Exterior m (C.filter (inUnion m)) (C \ C.filter (inUnion m)) := by
  constructor
  · intro x hx hi
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1, hi⟩)
  · have s : C.filter (inUnion m) ∪ (C \ C.filter (inUnion m)) ⊆ C :=
      Finset.union_subset (Finset.filter_subset _ _) Finset.sdiff_subset
    exact fun x hx y hy => hc x (s hx) y (s hy)

end SevenCycle.Adjacent
