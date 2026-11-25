import LeastPrime.Checker.TargetIntegration
import LeastPrime.Checker.GapEstimate
import LeastPrime.StickLastPieces

/-! Soundness of the piecewise-affine level-two integration. -/

namespace LeastPrime.Checker

open MeasureTheory Set

noncomputable section

private theorem gapCuts_mem {bound : Bound} {passed : GridSet} {a b c : Nat} :
    c ∈ gapCuts bound passed a b ↔
      c = a ∨ c = b ∨ (c ∈ breakpointCandidates bound passed ∧ a < c ∧ c < b) := by
  simp only [gapCuts, List.mem_mergeSort, List.mem_cons, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]

private theorem gapCuts_sorted (bound : Bound) (passed : GridSet) (a b : Nat) :
    (gapCuts bound passed a b).Pairwise (· ≤ ·) := by
  let cuts := a :: b :: (breakpointCandidates bound passed).filter (fun cut => a < cut && cut < b)
  have hs : (cuts.mergeSort).Pairwise (fun x y : Nat => decide (x ≤ y) = true) := by
    apply List.pairwise_mergeSort
    · intro x y z hxy hyz
      simpa only [decide_eq_true_eq] using (of_decide_eq_true hxy).trans (of_decide_eq_true hyz)
    · intro x y
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total x y
  simpa only [decide_eq_true_eq] using hs

private theorem cutBounds {bound : Bound} {passed : GridSet} {a b c : Nat} (hab : a ≤ b)
    (hc : c ∈ gapCuts bound passed a b) : a ≤ c ∧ c ≤ b := by
  rcases gapCuts_mem.mp hc with rfl | rfl | ⟨_, hca, hcb⟩
  · exact ⟨le_rfl, hab⟩
  · exact ⟨hab, le_rfl⟩
  · exact ⟨hca.le, hcb.le⟩

private theorem le_getLastD {a x : Nat} {rest : List Nat} (hs : (a :: rest).Pairwise (· ≤ ·))
    (hx : x ∈ a :: rest) : x ≤ rest.getLastD a := by
  induction rest generalizing a with
  | nil =>
    simpa only [List.mem_singleton, List.getLastD_nil] using
      (List.mem_singleton.mp hx).le
  | cons b rest ih =>
    rw [List.getLastD_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · have hmem := List.getLastD_mem_cons (l := rest) (a := b)
      exact (List.pairwise_cons.mp hs).1 _ hmem
    · exact ih hs.tail hx

private def availableReal (bound : Bound) (passed : GridSet) (r : ℝ) : ℝ :=
  match bound with
  | .lower => gLower r (denote passed)
  | .upper => gUpper r (denote passed)

private theorem finalGap_cell_correct (bound : Bound)
    {T passed pending : GridSet} (ht : T = passed.reverse ++ pending)
    (hT : Valid T) (h0 : 0 ∉ denote T) {a b x y : Nat}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ unit)
    (hp : ∀ I ∈ passed, I.2 ≤ a) (hq : ∀ I ∈ pending, b ≤ I.1)
    (hxy : Adjacent x y (gapCuts bound passed a b)) (hxy_le : x ≤ y) :
    Bounds bound (area ((y - x) * estimatedProbability bound x y
      (availableLength bound passed x) (availableLength bound passed y)))
      (∫ r in Icc (grid x) (grid y), probabilityFor bound 1 (residualTarget r (denote T))) := by
  by_cases heq : x = y
  · subst y
    rw [Nat.sub_self, zero_mul, area_zero, integral_grid_self]
    exact Bounds.refl _ _
  have hx := (cutBounds hab hxy.left_mem).1
  have hy := (cutBounds hab hxy.right_mem).2
  have hlt : x < y := lt_of_le_of_ne hxy_le heq
  have hxn := ha.trans_le hx
  have hg : ∀ I ∈ passed, Good I := fun I hI => hT.1 I (mem_passed ht hI)
  have hdesc := passed_descending hT.2.1 ht
  have hc (c : Nat) (hmem : c ∈ breakpointCandidates bound passed) : ¬ (x < c ∧ c < y) := by
    rintro ⟨hxc, hcy⟩
    have hcut : c ∈ gapCuts bound passed a b :=
      gapCuts_mem.mpr (Or.inr (Or.inr ⟨hmem, hx.trans_lt hxc, hcy.trans_le hy⟩))
    exact (hxy.no_interior (gapCuts_sorted bound passed a b) hcut) ⟨hxc, hcy⟩
  have hE : EqOn (fun r => probabilityFor bound 1 (residualTarget r (denote T)))
      (fun r => availableReal bound passed r / r) (Ioo (grid x) (grid y)) := by
    intro r hr
    have hr' : r ∈ Ioo (grid a) (grid b) :=
      ⟨(grid_le_iff.mpr hx).trans_lt hr.1, hr.2.trans_le (grid_le_iff.mpr hy)⟩
    have hr1 : r ∈ Ioc (0 : ℝ) 1 := ⟨(grid_nonneg _).trans_lt hr'.1, hr'.2.le.trans (by
      rw [← grid_unit, grid_le_iff]; exact hb)⟩
    have he := denote_inter_gap ht hp hq hr'
    have hrT := not_mem_gap ht hp hq hr'
    have hclosed := isClosedTarget_denote hT.1
    cases bound
    · change p 1 (residualTarget r (denote T)) = gLower r (denote passed) / r
      rw [p_one_rescaled hclosed hT.2.2 h0 hr1 hrT, he]
    · change q 1 (residualTarget r (denote T)) = gUpper r (denote passed) / r
      rw [q_one_rescaled hclosed hT.2.2 h0 hr1 hrT, he]
  rw [area_mul, integral_grid_congr hE]
  have hp' (I : GridInterval) (hI : I ∈ passed) : I.2 ≤ x := (hp I hI).trans hx
  cases bound
  · exact lower_cell_estimate hxn hlt hg hdesc hp' hc
  · exact upper_cell_estimate hxn hlt hg hdesc hp' hc

theorem finalGap_correct (bound : Bound) {T passed pending : GridSet}
    (ht : T = passed.reverse ++ pending) (hT : Valid T) (h0 : 0 ∉ denote T)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ unit)
    (hp : ∀ I ∈ passed, I.2 ≤ a) (hq : ∀ I ∈ pending, b ≤ I.1) :
    Bounds bound (area (finalGap bound passed a b))
      (∫ r in Icc (grid a) (grid b), probabilityFor bound 1 (residualTarget r (denote T))) := by
  by_cases hz : passed = []
  · subst passed
    rw [empty_prefix_integral bound 1 ht hq]
    simp only [finalGap, List.isEmpty_nil, Bool.true_or, if_true, area_zero]
    exact Bounds.refl _ _
  by_cases heq : a = b
  · subst b
    rw [integral_grid_self]
    simp only [finalGap, beq_self_eq_true, Bool.or_true, if_true, area_zero]
    exact Bounds.refl _ _
  have ha := passed_pos ht h0 hp hT.1 hz
  have hEmpty : passed.isEmpty = false := by
    cases passed <;> simp_all
  have hbeq : (a == b) = false := by simp [heq]
  simp only [finalGap, hEmpty, hbeq, Bool.false_or, Bool.false_eq_true, if_false]
  have hfirst : a ∈ gapCuts bound passed a b := gapCuts_mem.mpr (Or.inl rfl)
  have hlast : b ∈ gapCuts bound passed a b := gapCuts_mem.mpr (Or.inr (Or.inl rfl))
  have hsort := gapCuts_sorted bound passed a b
  split
  · rename_i hempty
    simp [hempty] at hfirst
  · rename_i start rest hc
    have hrange (c : Nat) (hc' : c ∈ start :: rest) : a ≤ c ∧ c ≤ b :=
      cutBounds hab (hc ▸ hc')
    rw [hc] at hfirst hlast hsort
    have hstart : start = a := by
      refine le_antisymm ?_ (hrange start List.mem_cons_self).1
      rcases List.mem_cons.mp hfirst with h | h
      · omega
      · exact (List.pairwise_cons.mp hsort).1 _ h
    subst start
    have hend : rest.getLastD a = b :=
      le_antisymm (hrange _ List.getLastD_mem_cons).2 (le_getLastD hsort hlast)
    have hf := probabilityFor_residual_integrable bound 1 (isClosedTarget_denote hT.1) hT.2.2
    have hfb : IntegrableOn (fun r => probabilityFor bound 1 (residualTarget r (denote T)))
        (Icc (grid a) (grid b)) :=
      hf.mono_set (Icc_subset_Icc (grid_nonneg _) (by rw [← grid_unit, grid_le_iff]; exact hb))
    conv_rhs => rw [← hend]
    apply sumCutCells_correct bound _ _ hsort (hend ▸ hfb)
    intro x y hxy hxy_le
    exact finalGap_cell_correct bound ht hT h0 ha hab hb hp hq (hc.symm ▸ hxy) hxy_le

end

end LeastPrime.Checker
