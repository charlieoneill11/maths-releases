import LeastPrime.StickRecursion
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The exact formulas for the final two breaks. -/

namespace LeastPrime

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

theorem closedTarget_isCompact {T : Set ℝ} (hT : IsClosedTarget T) : IsCompact T :=
  isCompact_Icc.of_isClosed_subset (closedTarget_isClosed hT) (closedTarget_subset hT)

private theorem simplex_one_iff {v : Fin 1 → ℝ} :
    v ∈ simplex 1 ↔ v 0 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact fun h => h.1 0
  · intro h
    refine ⟨fun i => ?_, by simpa using h.2⟩
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using h

private theorem finset_fin_one (S : Finset (Fin 1)) : S = ∅ ∨ S = {0} := by
  by_cases h : (0 : Fin 1) ∈ S
  · right
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using h
  · left
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using h

private theorem remainder_one (v : Fin 1 → ℝ) : remainder v = 1 - v 0 := by simp [remainder]

private theorem measureReal_coord_one {T : Set ℝ} (hT : MeasurableSet T)
    (hUnit : T ⊆ Icc 0 1) :
    (stickLaw 1).real ((fun v : Fin 1 → ℝ => v 0) ⁻¹' T) = volume.real T := by
  rw [← map_measureReal_apply (measurable_pi_apply 0) hT, stickLaw_one,
    measureReal_restrict_apply hT, inter_eq_left.mpr hUnit]

/-- In one break an endpoint-only witness in a symmetric target must be one of the two pieces,
unless zero is itself in the target. -/
theorem p_one {T : Set ℝ} (hT : IsClosedTarget T) (hs : IsSymmetric T) (hzero : 0 ∉ T) :
    p 1 T = volume.real T := by
  have hone : 1 ∉ T := by
    intro ht
    exact hzero (by simpa using symmetric_sub hs ht)
  have heq : stickEvent true 1 T = (fun v : Fin 1 → ℝ => v 0) ⁻¹' T := by
    ext v
    constructor
    · rintro ⟨_, S, y, hy, h⟩
      rcases finset_fin_one S with rfl | rfl <;>
        rcases (show y = 0 ∨ y = remainder v from hy) with rfl | rfl
      · exact (hzero (by simpa [subsetSum] using h)).elim
      · have h' : 1 - v 0 ∈ T := by simpa [subsetSum, remainder_one] using h
        simpa only [sub_sub_cancel] using symmetric_sub hs h'
      · simpa [subsetSum] using h
      · have hn : v 0 + (1 - v 0) = 1 := by ring
        exact (hone (by simpa [subsetSum, remainder_one, hn] using h)).elim
    · intro h
      refine ⟨simplex_one_iff.mpr (closedTarget_subset hT h), {0}, 0, Or.inl rfl, ?_⟩
      simpa [subsetSum] using h
  rw [← probability_true, probability, heq]
  exact measureReal_coord_one (closedTarget_isClosed hT).measurableSet (closedTarget_subset hT)

/-- In one break any smaller first piece can be topped up to the greatest target point. -/
theorem q_one {T : Set ℝ} (hT : IsClosedTarget T) (hs : IsSymmetric T)
    (hNonempty : T.Nonempty) : q 1 T = sSup T := by
  let m := sSup T
  have hm : m ∈ T := (closedTarget_isCompact hT).sSup_mem hNonempty
  have hmUnit := closedTarget_subset hT hm
  have hmax (x : ℝ) (hx : x ∈ T) : x ≤ m :=
    le_csSup (bddAbove_Icc.mono (closedTarget_subset hT)) hx
  have heq : stickEvent false 1 T = (fun v : Fin 1 → ℝ => v 0) ⁻¹' Icc 0 m := by
    ext v
    constructor
    · rintro ⟨hv, S, y, hy, ht⟩
      change y ∈ Icc 0 (remainder v) at hy
      have hvUnit := simplex_one_iff.mp hv
      refine ⟨hvUnit.1, ?_⟩
      rcases finset_fin_one S with rfl | rfl
      · have hyT : y ∈ T := by simpa [subsetSum] using ht
        have hyUpper : y ≤ 1 - v 0 := by simpa only [remainder_one] using hy.2
        linarith [hmax (1 - y) (symmetric_sub hs hyT)]
      · have hyT : v 0 + y ∈ T := by simpa [subsetSum] using ht
        linarith [hmax (v 0 + y) hyT, hy.1]
    · intro hv
      change v 0 ∈ Icc 0 m at hv
      refine ⟨simplex_one_iff.mpr ⟨hv.1, hv.2.trans hmUnit.2⟩, {0}, m - v 0, ?_, ?_⟩
      · change m - v 0 ∈ Icc 0 (remainder v)
        rw [remainder_one]
        exact ⟨sub_nonneg.mpr hv.2, sub_le_sub_right hmUnit.2 _⟩
      · simp only [subsetSum, Finset.sum_singleton, add_sub_cancel]
        exact hm
  rw [← probability_false, probability, heq,
    measureReal_coord_one measurableSet_Icc (Icc_subset_Icc_right hmUnit.2), Real.volume_real_Icc]
  simp only [sub_zero, max_eq_left hmUnit.1]
  rfl

private theorem residual_no_zero {T : Set ℝ} {r : ℝ}
    (hr : 0 < r) (hzero : 0 ∉ T) (hrT : r ∉ T) : 0 ∉ residualTarget r T := by
  rintro (h | ⟨t, ht, heq⟩)
  · exact hzero (by simpa using ((mem_rescale_iff hr).mp h).1)
  · have ht₁ : t = 1 := by
      change 1 - t = 0 at heq
      linarith
    exact hrT (by simpa [ht₁] using ((mem_rescale_iff hr).mp ht).1)

private theorem residual_as_preimage {r : ℝ} {T : Set ℝ} (hr : 0 < r) :
    residualTarget r T =
      (fun x => r * x) ⁻¹' ((T ∩ Icc 0 r) ∪ (fun w => r - w) '' (T ∩ Icc 0 r)) := by
  ext x
  constructor
  · rintro (⟨w, hw, rfl⟩ | ⟨t, ⟨w, hw, rfl⟩, rfl⟩)
    · left
      change r * (w / r) ∈ T ∩ Icc 0 r
      simpa [mul_div_cancel₀ _ hr.ne'] using hw
    · right
      refine ⟨w, hw, ?_⟩
      change r - w = r * (1 - w / r)
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hr.ne']
  · rintro (hx | ⟨w, hw, heq⟩)
    · exact Or.inl ⟨r * x, hx, by change r * x / r = x; rw [mul_comm, mul_div_cancel_right₀ _ hr.ne']⟩
    · right
      refine ⟨w / r, ⟨w, hw, rfl⟩, ?_⟩
      change 1 - w / r = x
      have heq' : r - w = r * x := heq
      apply (mul_right_inj' hr.ne').mp
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hr.ne', heq']

theorem p_one_rescaled {T : Set ℝ} (hT : IsClosedTarget T) (_hs : IsSymmetric T)
    (hzero : 0 ∉ T) {r : ℝ} (hr : r ∈ Ioc 0 1) (hrT : r ∉ T) :
    p 1 (residualTarget r T) = gLower r (T ∩ Icc 0 r) / r := by
  rw [p_one (residualTarget_closedTarget hT hr.1) (residualTarget_symmetric r T)
    (residual_no_zero hr.1 hzero hrT), residual_as_preimage hr.1]
  simp only [gLower, measureReal_def, Real.volume_preimage_mul_left hr.1.ne', ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hr.1.le), abs_of_pos (inv_pos.mpr hr.1),
    div_eq_mul_inv, mul_comm]

private theorem residual_empty {T : Set ℝ} {r : ℝ} (h : T ∩ Icc 0 r = ∅) :
    residualTarget r T = ∅ := by simp [residualTarget, rescale, reflect, h]

theorem q_one_rescaled {T : Set ℝ} (hT : IsClosedTarget T) (_hs : IsSymmetric T)
    (_hzero : 0 ∉ T) {r : ℝ} (hr : r ∈ Ioc 0 1) (_hrT : r ∉ T) :
    q 1 (residualTarget r T) = gUpper r (T ∩ Icc 0 r) / r := by
  classical
  let W := T ∩ Icc 0 r
  by_cases hW : W.Nonempty
  · have hcompact : IsCompact W := (closedTarget_isCompact hT).inter_right isClosed_Icc
    have hMin : sInf W ∈ W := hcompact.sInf_mem hW
    have hMax : sSup W ∈ W := hcompact.sSup_mem hW
    have hLo (x : ℝ) (hx : x ∈ W) : sInf W ≤ x :=
      csInf_le (bddBelow_Icc.mono (inter_subset_right (s := T))) hx
    have hHi (x : ℝ) (hx : x ∈ W) : x ≤ sSup W :=
      le_csSup (bddAbove_Icc.mono (inter_subset_right (s := T))) hx
    let a := sSup W / r
    let b := 1 - sInf W / r
    have ha : a ∈ residualTarget r T := Or.inl ⟨sSup W, hMax, rfl⟩
    have hb : b ∈ residualTarget r T := Or.inr ⟨sInf W / r, ⟨sInf W, hMin, rfl⟩, rfl⟩
    have hm : max a b ∈ residualTarget r T := by
      rcases le_total a b with h | h
      · simpa only [max_eq_right h] using hb
      · simpa only [max_eq_left h] using ha
    have hgreat : IsGreatest (residualTarget r T) (max a b) := by
      refine ⟨hm, ?_⟩
      rintro x (⟨w, hw, rfl⟩ | ⟨t, ⟨w, hw, rfl⟩, rfl⟩)
      · exact ((div_le_div_iff_of_pos_right hr.1).mpr (hHi w hw)).trans (le_max_left a b)
      · exact (sub_le_sub_left ((div_le_div_iff_of_pos_right hr.1).mpr (hLo w hw)) 1).trans
          (le_max_right a b)
    rw [q_one (residualTarget_closedTarget hT hr.1) (residualTarget_symmetric r T) ⟨_, hm⟩,
      hgreat.csSup_eq, gUpper, if_pos hW]
    change max (sSup W / r) (1 - sInf W / r) = max (r - sInf W) (sSup W) / r
    rw [← max_div_div_right hr.1.le, sub_div, div_self hr.1.ne', max_comm]
  · have he : W = ∅ := not_nonempty_iff_eq_empty.mp hW
    rw [residual_empty he, q_empty, gUpper, if_neg hW, zero_div]

private theorem probability_two (wholeOnly : Bool) {T : Set ℝ} (hT : IsClosedTarget T)
    (hs : IsSymmetric T) (hzero : 0 ∉ T) (g : ℝ → Set ℝ → ℝ)
    (hgap : ∀ r ∈ Ioc (0 : ℝ) 1, r ∉ T →
      probability wholeOnly 1 (residualTarget r T) = g r (T ∩ Icc 0 r) / r) :
    probability wholeOnly 2 T =
      volume.real T + ∫ r in Icc (0 : ℝ) 1 \ T, g r (T ∩ Icc 0 r) / r := by
  let f := fun r => probability wholeOnly 1 (residualTarget r T)
  have hint : IntegrableOn f (Icc (0 : ℝ) 1) := (probability_recursion wholeOnly 1 hT hs).2
  have hmT := (closedTarget_isClosed hT).measurableSet
  have hTsub := closedTarget_subset hT
  have hTdisj : Disjoint T (Icc (0 : ℝ) 1 \ T) := disjoint_sdiff_right
  have hGapMeas : MeasurableSet (Icc (0 : ℝ) 1 \ T) := measurableSet_Icc.diff hmT
  have hunion : T ∪ (Icc (0 : ℝ) 1 \ T) = Icc 0 1 := union_diff_cancel hTsub
  have ht : (∫ r in T, f r) = volume.real T := by
    trans ∫ _ in T, (1 : ℝ)
    · apply setIntegral_congr_fun hmT
      intro r hr
      have hr' : 0 < r := lt_of_le_of_ne (hTsub hr).1 (fun h => hzero (h ▸ hr))
      exact probability_residual_one wholeOnly 1 hr' hr
    · simp
  have hg : (∫ r in Icc (0 : ℝ) 1 \ T, f r) =
      ∫ r in Icc (0 : ℝ) 1 \ T, g r (T ∩ Icc 0 r) / r := by
    apply setIntegral_congr_fun hGapMeas
    intro r hr
    by_cases h : r = 0
    · subst r
      have he : T ∩ Icc (0 : ℝ) 0 = ∅ := by
        simpa [Icc_self] using disjoint_singleton_right.mpr hzero |>.inter_eq
      simp [f, residual_empty he, probability_empty]
    · exact hgap r ⟨lt_of_le_of_ne hr.1.1 (Ne.symm h), hr.1.2⟩ hr.2
  calc
    probability wholeOnly 2 T = ∫ r in Icc (0 : ℝ) 1, f r := (probability_recursion wholeOnly 1 hT hs).1
    _ = (∫ r in T, f r) + ∫ r in Icc (0 : ℝ) 1 \ T, f r := by
      rw [← setIntegral_union hTdisj hGapMeas (hint.mono_set hTsub)
        (hint.mono_set diff_subset), hunion]
    _ = _ := by rw [ht, hg]

theorem p_two {T : Set ℝ} (hT : IsClosedTarget T) (hs : IsSymmetric T) (hzero : 0 ∉ T) :
    p 2 T = volume.real T + ∫ r in Icc (0 : ℝ) 1 \ T, gLower r (T ∩ Icc 0 r) / r := by
  simpa only [probability_true] using probability_two true hT hs hzero gLower
    (fun r hr hrt => (probability_true _ _).trans (p_one_rescaled hT hs hzero hr hrt))

theorem q_two {T : Set ℝ} (hT : IsClosedTarget T) (hs : IsSymmetric T) (hzero : 0 ∉ T) :
    q 2 T = volume.real T + ∫ r in Icc (0 : ℝ) 1 \ T, gUpper r (T ∩ Icc 0 r) / r :=
  probability_two false hT hs hzero gUpper (fun _ hr hrt => q_one_rescaled hT hs hzero hr hrt)

end

end LeastPrime
