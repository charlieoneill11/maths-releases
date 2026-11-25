import LeastPrime.Checker.Integrate
import LeastPrime.Checker.Scaled
import LeastPrime.StickRecursion

/-! The recursive integration over the ordered target intervals and gaps. -/

namespace LeastPrime.Checker

open MeasureTheory Set

noncomputable section

def probabilityFor (bound : Bound) (k : Nat) (T : Set ℝ) : ℝ :=
  match bound with
  | .lower => p k T
  | .upper => q k T

theorem probabilityFor_empty (bound : Bound) (k : Nat) : probabilityFor bound k ∅ = 0 := by
  cases bound
  · exact p_empty k
  · exact q_empty k

theorem probabilityFor_zero_mem {T : Set ℝ} (bound : Bound) (k : Nat) (hT : 0 ∈ T) :
    probabilityFor bound k T = 1 := by
  cases bound
  · exact p_one_of_zero_mem hT
  · exact q_one_of_zero_mem hT

theorem probabilityFor_recursion (bound : Bound) (k : Nat) {T : Set ℝ}
    (hT : IsClosedTarget T) (hs : IsSymmetric T) :
    probabilityFor bound (k + 1) T =
      ∫ r in Icc (0 : ℝ) 1, probabilityFor bound k (residualTarget r T) := by
  cases bound
  · exact p_recursion k hT hs
  · exact q_recursion k hT hs

theorem probabilityFor_residual_integrable (bound : Bound) (k : Nat) {T : Set ℝ}
    (hT : IsClosedTarget T) (hs : IsSymmetric T) :
    IntegrableOn (fun r => probabilityFor bound k (residualTarget r T)) (Icc (0 : ℝ) 1) := by
  cases bound
  · exact p_residual_integrable k hT hs
  · exact q_residual_integrable k hT hs

theorem probabilityFor_residual_one (bound : Bound) (k : Nat) {T : Set ℝ} {r : ℝ}
    (hr : 0 < r) (hT : r ∈ T) : probabilityFor bound k (residualTarget r T) = 1 := by
  cases bound
  · exact p_residual_one k hr hT
  · exact q_residual_one k hr hT

theorem mem_passed {T passed rest : GridSet} (ht : T = passed.reverse ++ rest)
    {I : GridInterval} (hi : I ∈ passed) : I ∈ T := by
  rw [ht]
  exact List.mem_append_left _ (List.mem_reverse.mpr hi)

theorem mem_pending {T passed rest : GridSet} (ht : T = passed.reverse ++ rest)
    {I : GridInterval} (hi : I ∈ rest) : I ∈ T := by
  rw [ht]
  exact List.mem_append_right _ hi

theorem pending_segregated {T passed rest : GridSet} (hs : Segregated T)
    (ht : T = passed.reverse ++ rest) : Segregated rest := by
  rw [Segregated, ht, List.pairwise_append] at hs
  exact hs.2.1

theorem passed_descending {T passed rest : GridSet} (hs : Segregated T)
    (ht : T = passed.reverse ++ rest) : passed.Pairwise (fun I J => J.2 < I.1) := by
  rw [Segregated, ht, List.pairwise_append, List.pairwise_reverse] at hs
  exact hs.1

/-- For an interior point of a gap, intersecting the full target with the interval to its left
gives exactly the already traversed part. -/
theorem denote_inter_gap {T passed rest : GridSet} (ht : T = passed.reverse ++ rest)
    {a b : Nat} (hp : ∀ I ∈ passed, I.2 ≤ a) (hq : ∀ I ∈ rest, b ≤ I.1)
    {r : ℝ} (hr : r ∈ Ioo (grid a) (grid b)) :
    denote T ∩ Icc 0 r = denote passed := by
  ext x
  constructor
  · rintro ⟨hx, hxR⟩
    obtain ⟨I, hI, hxI⟩ := mem_denote.mp hx
    rw [ht, List.mem_append] at hI
    rcases hI with hI | hI
    · exact mem_denote.mpr ⟨I, List.mem_reverse.mp hI, hxI⟩
    · exact (not_le_of_gt hr.2 (le_trans (hxI.1.trans' (grid_le_iff.mpr (hq I hI))) hxR.2)).elim
  · intro hx
    obtain ⟨I, hI, hxI⟩ := mem_denote.mp hx
    exact ⟨mem_denote.mpr ⟨I, mem_passed ht hI, hxI⟩, (grid_nonneg _).trans hxI.1,
      hxI.2.trans ((grid_le_iff.mpr (hp I hI)).trans hr.1.le)⟩

theorem not_mem_gap {T passed rest : GridSet} (ht : T = passed.reverse ++ rest)
    {a b : Nat} (hp : ∀ I ∈ passed, I.2 ≤ a) (hq : ∀ I ∈ rest, b ≤ I.1)
    {r : ℝ} (hr : r ∈ Ioo (grid a) (grid b)) : r ∉ denote T := by
  intro hx
  have hpre := denote_inter_gap ht hp hq hr
  have hsub : r ∈ denote T ∩ Icc 0 r := ⟨hx, (grid_nonneg _).trans hr.1.le, le_rfl⟩
  rw [hpre] at hsub
  obtain ⟨I, hI, hxI⟩ := mem_denote.mp hsub
  exact not_le_of_gt hr.1 (hxI.2.trans (grid_le_iff.mpr (hp I hI)))

theorem passed_pos {T passed rest : GridSet} (ht : T = passed.reverse ++ rest)
    (h0 : 0 ∉ denote T) {a : Nat} (hp : ∀ I ∈ passed, I.2 ≤ a)
    (hGood : ∀ I ∈ T, Good I) (hn : passed ≠ []) : 0 < a := by
  by_contra! hz
  have ha : a = 0 := Nat.eq_zero_of_le_zero hz
  obtain ⟨I, hi⟩ := List.exists_mem_of_ne_nil passed hn
  have hmem := mem_passed ht hi
  have hhigh := hp I hi
  have hlow := (hGood I hmem).1
  have hh : I.2 = 0 := by omega
  have hl : I.1 = 0 := by omega
  exact h0 (mem_denote.mpr ⟨I, hmem, by simp [interval, hl, hh]⟩)

theorem empty_prefix_integral (bound : Bound) (k : Nat) {T rest : GridSet}
    (ht : T = ([] : GridSet).reverse ++ rest) {a b : Nat}
    (hq : ∀ I ∈ rest, b ≤ I.1) :
    (∫ r in Icc (grid a) (grid b), probabilityFor bound k (residualTarget r (denote T))) = 0 := by
  have hzero : EqOn (fun r => probabilityFor bound k (residualTarget r (denote T)))
      (fun _ => 0) (Ioo (grid a) (grid b)) := by
    intro r hr
    have h := denote_inter_gap ht (a := a) (by simp) hq hr
    change denote T ∩ Icc 0 r = ∅ at h
    change probabilityFor bound k (residualTarget r (denote T)) = 0
    rw [residualTarget, rescale, h, image_empty, reflect, image_empty, empty_union,
      probabilityFor_empty]
  rw [integral_grid_congr hzero]
  simp

private theorem residual_mono_for_bound {bound : Bound} {k : Nat} {S T : Set ℝ}
    (h : match bound with | .lower => S ⊆ T | .upper => T ⊆ S) :
    Bounds bound (probabilityFor bound k S) (probabilityFor bound k T) := by
  cases bound
  · exact p_mono h
  · exact q_mono h

theorem higherGap_correct (bound : Bound) (k : Nat) (recursive : GridSet → Nat)
    (step : Nat) {T passed rest : GridSet} (ht : T = passed.reverse ++ rest)
    (hT : Valid T) (h0 : 0 ∉ denote T) {a b : Nat} (hab : a ≤ b) (hb : b ≤ unit)
    (hp : ∀ I ∈ passed, I.2 ≤ a) (hq : ∀ I ∈ rest, b ≤ I.1)
    (hRec : ∀ S, Valid S → Bounds bound (grid (recursive S)) (probabilityFor bound k (denote S))) :
    Bounds bound (area (higherGap bound step recursive passed a b))
      (∫ r in Icc (grid a) (grid b), probabilityFor bound k (residualTarget r (denote T))) := by
  by_cases hz : passed = []
  · subst passed
    rw [empty_prefix_integral bound k ht hq]
    simp only [higherGap, List.isEmpty_nil, if_true, area_zero]
    exact Bounds.refl _ _
  · have ha := passed_pos ht h0 hp hT.1 hz
    have hi : ∀ I ∈ passed, Good I := fun I hI => hT.1 I (mem_passed ht hI)
    have hf := probabilityFor_residual_integrable bound k (isClosedTarget_denote hT.1) hT.2.2
    have hfb : IntegrableOn (fun r => probabilityFor bound k (residualTarget r (denote T)))
        (Icc (grid a) (grid b)) :=
      hf.mono_set (Icc_subset_Icc (grid_nonneg _) (by rw [← grid_unit, grid_le_iff]; exact hb))
    have hEmpty := List.isEmpty_eq_false_iff.mpr hz
    simp only [higherGap, hEmpty, Bool.false_eq_true, if_false]
    apply sumGridCells_correct bound _ _ step a b hab hfb
    intro x y hax hxy hyb
    have hGood : Valid (scaledTarget bound passed x y) :=
      scaledTarget_valid (ha.trans_le hax) hxy.le hi (fun I hI => (hp I hI).trans hax)
    have hfy : IntegrableOn (fun r => probabilityFor bound k (residualTarget r (denote T)))
        (Icc (grid x) (grid y)) :=
      hfb.mono_set (Icc_subset_Icc (grid_le_iff.mpr hax) (grid_le_iff.mpr hyb))
    apply constant_cell_bounds bound hxy.le hfy
    intro r hr
    have hr' : r ∈ Ioo (grid a) (grid b) :=
      ⟨(grid_le_iff.mpr hax).trans_lt hr.1, hr.2.trans_le (grid_le_iff.mpr hyb)⟩
    apply (hRec _ hGood).trans
    apply residual_mono_for_bound
    have hpre := denote_inter_gap ht hp hq hr'
    have hxi (I : GridInterval) (hI : I ∈ passed) : I.2 ≤ x := (hp I hI).trans hax
    cases bound
    · exact scaledTarget_lower_subset (ha.trans_le hax) hr hi hxi hpre
    · exact residualTarget_subset_scaledUpper (ha.trans_le hax) hr hi hxi hpre

/-- Partition an integrable function whose value is one inside target intervals, using
a sound bound on each gap. -/
theorem integrateTarget_correct (bound : Bound) (f : ℝ → ℝ) (gap : GridSet → Nat → Nat → Nat)
    {T : GridSet} (hT : Valid T)
    (hf : IntegrableOn f (Icc (0 : ℝ) 1)) (hOne : ∀ r ∈ denote T, 0 < r → f r = 1)
    (hGap : ∀ passed rest a b, T = passed.reverse ++ rest → a ≤ b → b ≤ unit →
      (∀ I ∈ passed, I.2 ≤ a) → (∀ I ∈ rest, b ≤ I.1) →
        Bounds bound (area (gap passed a b)) (∫ r in Icc (grid a) (grid b), f r)) :
    Bounds bound (area (integrateTarget gap [] 0 T)) (∫ r in Icc (0 : ℝ) 1, f r) := by
  have aux (rest passed : GridSet) (a : Nat) (ht : T = passed.reverse ++ rest) (ha : a ≤ unit)
      (hp : ∀ I ∈ passed, I.2 ≤ a) (hq : ∀ I ∈ rest, a ≤ I.1) :
      Bounds bound (area (integrateTarget gap passed a rest))
        (∫ r in Icc (grid a) (grid unit), f r) := by
    induction rest generalizing passed a with
    | nil =>
      exact hGap passed [] a unit ht ha le_rfl hp (by simp)
    | cons I rest ih =>
      have hI := hT.1 I (mem_pending ht List.mem_cons_self)
      have hL := hq I List.mem_cons_self
      have hLunit := hI.1.trans hI.2
      have hsg := pending_segregated hT.2.1 ht
      have hrest (J : GridInterval) (hj : J ∈ rest) : I.2 ≤ J.1 :=
        ((List.pairwise_cons.mp hsg).1 J hj).le
      have hPassed (J : GridInterval) (hj : J ∈ I :: passed) : J.2 ≤ I.2 := by
        rcases List.mem_cons.mp hj with rfl | hj
        · exact le_rfl
        · exact (hp J hj).trans (hL.trans hI.1)
      have hT' : T = (I :: passed).reverse ++ rest := by
        simpa [List.reverse_cons, List.append_assoc] using ht
      have hGap' := hGap passed (I :: rest) a I.1 ht hL hLunit hp (by
        intro J hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact le_rfl
        · exact hI.1.trans (hrest J hj))
      have hNext := ih (I :: passed) I.2 hT' hI.2 hPassed hrest
      have hM : (∫ r in Icc (grid I.1) (grid I.2), f r) = area (width I * unit) := by
        rw [area_mul, width, grid_sub hI.1, grid_unit, ← integral_grid_const hI.1]
        apply integral_grid_congr
        intro r hr
        exact hOne r (mem_denote.mpr ⟨I, mem_pending ht List.mem_cons_self, ⟨hr.1.le, hr.2.le⟩⟩)
          ((grid_nonneg _).trans_lt hr.1)
      have hfa : IntegrableOn f (Icc (grid a) (grid unit)) := by
        rw [grid_unit]
        exact hf.mono_set (Icc_subset_Icc (grid_nonneg _) le_rfl)
      have hfI : IntegrableOn f (Icc (grid a) (grid I.2)) :=
        hfa.mono_set (Icc_subset_Icc le_rfl (grid_le_iff.mpr hI.2))
      rw [← integral_grid_add (hL.trans hI.1) hI.2 hfa,
        ← integral_grid_add hL hI.1 hfI, hM]
      simp only [integrateTarget, area_add]
      exact (hGap'.add (Bounds.refl _ _)).add hNext
  simpa only [grid_zero, grid_unit] using
    aux T [] 0 (by simp) (Nat.zero_le unit) (by simp) (fun _ _ => Nat.zero_le _)

end

end LeastPrime.Checker
