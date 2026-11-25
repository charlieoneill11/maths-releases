import LeastPrime.Checker.TargetIntegration
import LeastPrime.StickLastPieces

/-! The integer checker's zero- and one-break cases. -/

namespace LeastPrime.Checker

open MeasureTheory Set

noncomputable section

theorem zero_mem_denote_iff_head_zero {head : GridInterval} {tail : GridSet}
    (hT : Valid (head :: tail)) : 0 ∈ denote (head :: tail) ↔ head.1 = 0 := by
  constructor
  · intro hz
    obtain ⟨I, hi, hzi⟩ := mem_denote.mp hz
    have hI : I.1 = 0 := Nat.eq_zero_of_le_zero <| grid_le_iff.mp <| by simpa using hzi.1
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hI
    · have hlt := (List.pairwise_cons.mp hT.2.1).1 I hi
      omega
  · intro hz
    refine mem_denote.mpr ⟨head, List.mem_cons_self, ?_⟩
    exact ⟨by simp [hz], grid_nonneg _⟩

theorem denote_nonempty_of_cons {head : GridInterval} {tail : GridSet}
    (hT : Valid (head :: tail)) : (denote (head :: tail)).Nonempty :=
  ⟨grid head.2, mem_denote.mpr ⟨head, List.mem_cons_self,
    grid_le_iff.mpr (hT.1 head List.mem_cons_self).1, le_rfl⟩⟩

private theorem supremum_denote_eq_last {head : GridInterval} {tail : GridSet}
    (hT : Valid (head :: tail)) :
    sSup (denote (head :: tail)) = grid ((head :: tail).getLastD head).2 := by
  have hn : head :: tail ≠ [] := List.cons_ne_nil _ _
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hn, Option.getD_some]
  apply IsGreatest.csSup_eq
  have hlast := List.getLast_mem hn
  refine ⟨mem_denote.mpr ⟨_, hlast, grid_le_iff.mpr (hT.1 _ hlast).1, le_rfl⟩, ?_⟩
  intro x hx
  obtain ⟨I, hi, hmem⟩ := mem_denote.mp hx
  have hpair : (head :: tail).Pairwise (fun I J : GridInterval => I.2 ≤ J.2) :=
    List.Pairwise.imp_of_mem (fun {_ J} _ hj hij => (Nat.le_of_lt hij).trans (hT.1 J hj).1) hT.2.1
  exact hmem.2.trans (grid_le_iff.mpr (hpair.rel_getLast_of_rel_getLast_getLast hi le_rfl))

theorem probabilityBound_base (bound : Bound) (k : Nat) (targets : GridSet)
    (hk : k < 2) (hT : Valid targets) :
    Bounds bound (grid (probabilityBound bound k targets)) (probabilityFor bound k (denote targets)) := by
  cases targets with
  | nil =>
    rw [probabilityBound, denote, probabilityFor_empty, grid_zero]
    exact Bounds.refl bound 0
  | cons head tail =>
    by_cases hhead : head.1 = 0
    · have hz := (zero_mem_denote_iff_head_zero hT).mpr hhead
      rw [probabilityFor_zero_mem bound k hz, probabilityBound.eq_def]
      simp only [if_pos hhead, grid_unit]
      exact Bounds.refl bound 1
    · have hzero : 0 ∉ denote (head :: tail) := fun h =>
        hhead ((zero_mem_denote_iff_head_zero hT).mp h)
      have hClosed := isClosedTarget_denote hT.1
      have hs := hT.2.2
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;> cases bound
      · rw [probabilityBound.eq_def]
        simp only [if_neg hhead]
        change grid 0 ≤ p 0 (denote (head :: tail))
        rw [grid_zero]
        exact p_nonneg 0 _
      · rw [probabilityBound.eq_def]
        simp only [if_neg hhead]
        change q 0 (denote (head :: tail)) ≤ grid unit
        rw [grid_unit]
        exact q_le_one 0 _
      · rw [probabilityBound.eq_def]
        simp only [if_neg hhead]
        change grid (targetLength (head :: tail)) ≤ p 1 (denote (head :: tail))
        rw [p_one hClosed hs hzero, volume_denote hT.1 (disjointIntervals_of_segregated hT.2.1)]
      · rw [probabilityBound.eq_def]
        simp only [if_neg hhead]
        change q 1 (denote (head :: tail)) ≤ grid ((head :: tail).getLastD head).2
        rw [q_one hClosed hs (denote_nonempty_of_cons hT), supremum_denote_eq_last hT]

end

end LeastPrime.Checker
