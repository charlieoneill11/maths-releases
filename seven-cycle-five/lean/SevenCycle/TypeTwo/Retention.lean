import SevenCycle.TypeTwo.Matching
import SevenCycle.Adjacent.Retention
import SevenCycle.Proof.Deficits

/-! ## Type-two layouts induced by a code -/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry

private theorem plane_stripe_comm (C : Points) {k l : Axis} (h : k ≠ l) (s t : Height) :
    stripe (plane C k s) l t = plane (stripe C l t) k s :=
  face_comm C h (fun z => z = s) (fun z => z = t ∨ z = t+1)

theorem middle_union (C : Points) (k : Axis) (i : Height) :
    plane C k i ∪ plane C k (i+1) = stripe C k i :=
  plane_union C k i

theorem middle_disjoint {C : Points} (hc : packing cycleStep C) (k : Axis) (i : Height) :
    Disjoint (plane C k i) (plane C k (i+1)) :=
  planes_disjoint hc k i

private theorem second_start (m : Frame) (k : Axis) (hk : m.gap k = 2) :
    start m k true = (m.base k + 1) + 1 := by
  simp +decide [start, hk, add_assoc]

/-- Every true tuple of the six transverse projections passes all Stage 3
crossings, level prescriptions, and left/right conflict tests. -/
theorem projections_retain {C : Points} {m : Frame} {k : Axis} (hc : packing cycleStep C)
    (hm : Marked m C) (hk : m.gap k = 2) :
    TwoProjections m k (projections m C k false) (projections m C k true)
      (plane C k (m.base k+1)) (plane C k (start m k true)) (projections m C) := by
  refine ⟨projected_join hc hm k, ?_, ?_, ?_⟩
  · rw [second_start m k hk]
    exact middle_disjoint hc _ _
  · rw [second_start m k hk, middle_union]
    exact stripe_packing hc _ _
  · intro l hl b
    exact ⟨plane_stripe_comm C hl.symm _ _, plane_stripe_comm C hl.symm _ _⟩

/-- All Stage 2 constraints hold for the projections of a true code and every
perfect matching, using only the numerical level and middle-band bounds. -/
theorem middle_retains {C : Points} {m : Frame} {k : Axis} (hc : packing cycleStep C)
    (hm : Marked m C) (hk : m.gap k = 2)
    (hsizes : ∀ t, 14 ≤ (level C k t).card ∧ (level C k t).card ≤ 19)
    (hband : 31 ≤ (band C k (m.base k+1)).card)
    (M : Finset Edge) (hM : Perfect (projections m C k false) (projections m C k true) M) :
    TwoMiddle m k (projections m C k false) (projections m C k true)
      (plane C k (m.base k+1)) (plane C k (start m k true)) M := by
  obtain ⟨hj, hd, hu, hcuts⟩ := projections_retain hc hm hk
  have hX : plane C k (m.base k + 1) ⊆ projections m C k false :=
    Adjacent.plane_sub_stripe (Or.inr (by simp [start]))
  have hY : plane C k (start m k true) ⊆ projections m C k true :=
    Adjacent.plane_sub_stripe (Or.inl rfl)
  have hcard (t : Height) : (plane C k t).card = (level C k t).card := Adjacent.plane_card hc k t
  have hsum : 31 ≤ (plane C k (m.base k+1)).card + (plane C k (start m k true)).card := by
    rw [hcard, hcard, second_start m k hk]
    exact hband.trans_eq (Bands.band_card C k (m.base k+1))
  have h33 : (projections m C k false).card = 33 :=
    (face33 (k := k) (t := start m k false) hc (hm.2.1 k false)).1
  have bounds := matching_bounds hM hX hY hd hu h33 hsum
  refine ⟨hX, hY, ?_, ?_, ?_, ?_, bounds.1, bounds.2, ?_⟩
  · rw [hcard]; exact (hsizes _).1
  · rw [hcard]; exact (hsizes _).2
  · rw [hcard]; exact (hsizes _).1
  · rw [hcard]; exact (hsizes _).2
  · intro l hl b
    obtain ⟨hface, hfit⟩ := hj.1 l hl b
    exact ⟨projections m C l b, hface, hfit, hcuts l hl b⟩

/-- The stage retains every actual 113-code, once the three-dimensional upper
bound is supplied, for every choice of the perfect matching. -/
theorem middle_retains_113
    (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33)
    {C : Points} {m : Frame} {k : Axis} (hc : packing cycleStep C)
    (hm : Marked m C) (hk : m.gap k = 2) (h113 : C.card = 113) (hn : NoConsecutive C)
    (M : Finset Edge) (hM : Perfect (projections m C k false) (projections m C k true) M) :
    TwoMiddle m k (projections m C k false) (projections m C k true)
      (plane C k (m.base k+1)) (plane C k (start m k true)) M := by
  apply middle_retains hc hm hk (Deficits.deficits_one h3 C hc h113 k).2 _ M hM
  apply Deficits.deficits_three_at h3 C hc h113 k (m.base k) (hn k) (hm.2.1 k false)
  simpa [start, hk] using hm.2.1 k true

end SevenCycle.TypeTwo
