import Chowla.Model.Cumulants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

namespace Chowla

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def extremalA : ℝ := (1 + Real.cot (1 / 4)) / 8
private noncomputable def extremalB : ℝ := 1 / 4 - extremalA

private noncomputable def extremalPositive (u : ℝ) : ℝ :=
  extremalA * Real.cos (u / 2) + extremalB * Real.sin (u / 2)

private noncomputable def extremalPrimitive (u : ℝ) : ℝ :=
  2 * extremalA * Real.sin (u / 2) - 2 * extremalB * Real.cos (u / 2)

private theorem H_eq_indicator :
    H = (Icc (-1 : ℝ) 1).indicator (fun u => extremalPositive |u|) := rfl

theorem H_even : Function.Even H := by
  intro u
  have hmem : -u ∈ Icc (-1 : ℝ) 1 ↔ u ∈ Icc (-1 : ℝ) 1 := by
    simp only [mem_Icc, ← abs_le, abs_neg]
  simp only [H_eq_indicator, Set.indicator_apply, hmem, abs_neg]

theorem H_isProfile : IsProfile H := by
  refine ⟨?_, H_even, ?_, ?_⟩
  · rw [H_eq_indicator]
    apply Measurable.indicator _ measurableSet_Icc
    unfold extremalPositive
    fun_prop
  · refine isBounded_iff_forall_norm_le.mpr ⟨|extremalA| + |extremalB|, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [Real.norm_eq_abs, H_eq_indicator]
    by_cases hu : u ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hu, extremalPositive]
      calc
        _ ≤ |extremalA * Real.cos (|u| / 2)| + |extremalB * Real.sin (|u| / 2)| :=
          abs_add_le ..
        _ ≤ _ := by
          rw [abs_mul, abs_mul]
          simpa only [mul_one] using add_le_add
            (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
              (abs_nonneg extremalA))
            (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
              (abs_nonneg extremalB))
    · rw [Set.indicator_of_notMem hu, abs_zero]
      positivity
  · refine HasCompactSupport.intro (K := Icc (-1 : ℝ) 1) isCompact_Icc ?_
    intro u hu
    simp [H_eq_indicator, hu]

theorem H_hasRadiusAtMost : HasRadiusAtMost H 1 := by
  refine ⟨zero_le_one, ?_⟩
  filter_upwards with u hu
  simp [H_eq_indicator, hu]

private theorem H_eq_extremalPositive {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    H u = extremalPositive u := by
  rw [H_eq_indicator, Set.indicator_of_mem
    (show u ∈ Icc (-1 : ℝ) 1 from ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hu.1, hu.2⟩),
    abs_of_nonneg hu.1]

private theorem extremalA_formula :
    extremalA = (Real.cos (1 / 4) + Real.sin (1 / 4)) / (8 * Real.sin (1 / 4)) := by
  have hs : Real.sin (1 / 4) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])).ne'
  unfold extremalA
  rw [Real.cot_eq_cos_div_sin]
  field_simp
  ring

private theorem extremalB_formula :
    extremalB = (Real.sin (1 / 4) - Real.cos (1 / 4)) / (8 * Real.sin (1 / 4)) := by
  have hs : Real.sin (1 / 4) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])).ne'
  rw [extremalB, extremalA_formula]
  field_simp
  ring

private theorem extremal_half_turn :
    (extremalA * Real.sin (1 / 2) - extremalB * Real.cos (1 / 2) = extremalA) ∧
    (extremalA * Real.cos (1 / 2) + extremalB * Real.sin (1 / 2) = -extremalB) := by
  let c := Real.cos (1 / 4)
  let s := Real.sin (1 / 4)
  have hsq : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hsin : Real.sin (1 / 2) = 2 * s * c := by
    rw [show (1 / 2 : ℝ) = 2 * (1 / 4) by norm_num, Real.sin_two_mul]
  have hcos : Real.cos (1 / 2) = c ^ 2 - s ^ 2 := by
    rw [show (1 / 2 : ℝ) = 2 * (1 / 4) by norm_num, Real.cos_two_mul]
    change 2 * c ^ 2 - 1 = c ^ 2 - s ^ 2
    linarith
  have ha : extremalA = (c + s) / (8 * s) := extremalA_formula
  have hb : extremalB = (s - c) / (8 * s) := extremalB_formula
  rw [hsin, hcos, ha, hb]
  constructor
  · calc
      _ = (c + s) / (8 * s) * (c ^ 2 + s ^ 2) := by ring
      _ = _ := by rw [hsq, mul_one]
  · calc
      _ = (c - s) / (8 * s) * (c ^ 2 + s ^ 2) := by ring
      _ = _ := by rw [hsq]; ring

private theorem extremalPrimitive_reflection (u : ℝ) :
    extremalPrimitive (1 - u) = 2 * extremalPositive u := by
  rw [extremalPrimitive, extremalPositive,
    show (1 - u) / 2 = 1 / 2 - u / 2 by ring, Real.sin_sub, Real.cos_sub]
  calc
    _ = 2 * ((extremalA * Real.sin (1 / 2) - extremalB * Real.cos (1 / 2)) *
      Real.cos (u / 2) -
      (extremalA * Real.cos (1 / 2) + extremalB * Real.sin (1 / 2)) * Real.sin (u / 2)) :=
        by ring
    _ = _ := by rw [extremal_half_turn.1, extremal_half_turn.2]; ring

private theorem extremalPrimitive_zero : extremalPrimitive 0 = -2 * extremalB := by
  simp [extremalPrimitive]

private theorem extremalPrimitive_one : extremalPrimitive 1 = 2 * extremalA := by
  simpa [extremalPositive] using extremalPrimitive_reflection 0

private theorem integral_extremalPositive (a b : ℝ) :
    (∫ u in a..b, extremalPositive u) = extremalPrimitive b - extremalPrimitive a := by
  have hlin (u : ℝ) : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) u :=
    (hasDerivAt_id u).div_const 2
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u _
    have hsin := (Real.hasDerivAt_sin (u / 2)).comp u (hlin u)
    have hcos := (Real.hasDerivAt_cos (u / 2)).comp u (hlin u)
    convert (hsin.const_mul (2 * extremalA)).sub (hcos.const_mul (2 * extremalB)) using 1
    simp only [extremalPositive]
    ring
  · apply Continuous.intervalIntegrable
    unfold extremalPositive
    fun_prop

private theorem integral_H_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ u in (0 : ℝ)..t, H u) = extremalPrimitive t - extremalPrimitive 0 := by
  rw [← integral_extremalPositive]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.1]
  intro u hu
  exact H_eq_extremalPositive ⟨hu.1, hu.2.trans ht.2⟩

theorem integral_even_symm {f : FourierProfile} (hf : Integrable f) (he : Function.Even f)
    {b : ℝ} (_hb : 0 ≤ b) :
    (∫ x in (-b)..b, f x) = 2 * ∫ x in (0 : ℝ)..b, f x := by
  have hsym : (∫ x in (-b)..(0 : ℝ), f x) = ∫ x in (0 : ℝ)..b, f x := by
    simpa only [show ∀ x, f (-x) = f x from he, neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -b) (b := 0) f)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (a := -b) (b := 0)) (hf.intervalIntegrable (a := 0) (b := b)),
    hsym, two_mul]

/-- Lemma 21, normalisation of the extremal profile. -/
theorem integral_H : (∫ u : ℝ, H u) = 1 := by
  rw [H_eq_indicator, integral_indicator measurableSet_Icc]
  change (∫ u in Icc (-1 : ℝ) 1, extremalPositive |u|) = 1
  have hI : (∫ u in Icc (-1 : ℝ) 1, extremalPositive |u|) = ∫ u in Icc (-1 : ℝ) 1, H u := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp [H_eq_indicator, hu]
  rw [hI, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_even_symm (integrable_of_isProfile H_isProfile) H_even zero_le_one,
    integral_H_pos (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩),
    extremalPrimitive_one, extremalPrimitive_zero, extremalB]
  ring

private theorem integral_H_from_one {b : ℝ} (hb : 1 ≤ b) :
    (∫ u in (1 : ℝ)..b, H u) = 0 := by
  rw [intervalIntegral.integral_of_le hb]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := (1 : ℝ)) (b := b))] with u hu
  have hout : u ∉ Icc (-1 : ℝ) 1 := fun h => (not_lt_of_ge h.2) hu.1
  simp [H_eq_indicator, hout]

private theorem integral_H_window_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ u in (s - 1)..(s + 1), H u) =
      extremalPrimitive (1 - s) + extremalPrimitive 1 - 2 * extremalPrimitive 0 := by
  have hi := integrable_of_isProfile H_isProfile
  have hleft : (∫ u in (s - 1)..(0 : ℝ), H u) = ∫ u in (0 : ℝ)..(1 - s), H u := by
    simpa only [show ∀ x, H (-x) = H x from H_even, neg_zero,
      show -(s - 1) = 1 - s by ring] using
      (intervalIntegral.integral_comp_neg (a := s - 1) (b := 0) H)
  have hright : (∫ u in (1 : ℝ)..(s + 1), H u) = 0 :=
    integral_H_from_one (by linarith [hs.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (a := s - 1) (b := 0))
    (hi.intervalIntegrable (a := 0) (b := s + 1)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hi.intervalIntegrable (a := 0) (b := 1))
      (hi.intervalIntegrable (a := 1) (b := s + 1)),
    hleft, hright, add_zero,
    integral_H_pos (show 1 - s ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hs.2], by linarith [hs.1]⟩),
    integral_H_pos (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]
  ring

private noncomputable def extremalKernel (s : ℝ) : ℝ :=
  H s - (∫ u in (s - 1)..(s + 1), H u) / 2

private theorem extremalKernel_even : Function.Even extremalKernel := by
  intro s
  unfold extremalKernel
  rw [show H (-s) = H s from H_even s]
  have hs : (∫ u in (-s - 1)..(-s + 1), H u) = ∫ u in (s - 1)..(s + 1), H u := by
    simpa only [show ∀ u, H (-u) = H u from H_even,
      show -(-s + 1) = s - 1 by ring, show -(-s - 1) = s + 1 by ring] using
      (intervalIntegral.integral_comp_neg (a := -s - 1) (b := -s + 1) H)
  rw [hs]

private theorem extremalKernel_eq {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    extremalKernel s = (Real.cot (1 / 4) - 3) / 8 := by
  have hpositive (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      extremalKernel t = (Real.cot (1 / 4) - 3) / 8 := by
    rw [extremalKernel, H_eq_extremalPositive ht, integral_H_window_nonneg ht,
      extremalPrimitive_reflection, extremalPrimitive_one, extremalPrimitive_zero,
      extremalB, extremalA]
    ring
  by_cases h : 0 ≤ s
  · exact hpositive s ⟨h, hs.2⟩
  · rw [← extremalKernel_even s]
    exact hpositive (-s) ⟨by linarith, by linarith [hs.1]⟩

private theorem shifted_integral_H (s : ℝ) :
    (∫ u in Icc (-1 : ℝ) 1, H (u - s)) = ∫ u in (s - 1)..(s + 1), H u := by
  have he : (∫ u in Icc (-1 : ℝ) 1, H (u - s)) = ∫ u in Icc (-1 : ℝ) 1, H (s - u) := by
    apply integral_congr_ae
    filter_upwards with u
    rw [← neg_sub, show H (-(s - u)) = H (s - u) from H_even _]
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left, sub_neg_eq_add]

/-- Lemma 21. Convolution against the extremal profile computes a scalar multiple of the
integral of every even profile supported in the unit interval. -/
theorem extremal_cumulant (ρ : FourierProfile) (hρ : IsProfile ρ)
    (hs : HasRadiusAtMost ρ 1) :
    cumulant [convolve H ρ] = (Real.cot (1 / 4) - 3) / 8 * ∫ u : ℝ, ρ u := by
  have hiH := integrable_of_isProfile H_isProfile
  have hiρ := integrable_of_isProfile hρ
  have hprod : Integrable (Function.uncurry fun u s : ℝ => ρ s * H (u - s))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (hiρ.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hiH).mono_measure
      Measure.restrict_le_self
  have hsum : (∫ x in (0 : ℝ)..1, convolve H ρ x) =
      (∫ s : ℝ, ρ s * ∫ u in (s - 1)..(s + 1), H u) / 2 := by
    have hs' := integral_even_symm (integrable_convolve hiH hiρ)
      (convolve_isProfile H_isProfile hρ).2.1 (b := 1) zero_le_one
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc, convolve_comm H ρ] at hs'
    simp_rw [convolve_apply] at hs'
    rw [integral_integral_swap hprod] at hs'
    simp_rw [integral_const_mul, shifted_integral_H] at hs'
    rw [convolve_comm H ρ]
    simp_rw [convolve_apply]
    linarith
  have hzero : convolve H ρ 0 = ∫ s : ℝ, ρ s * H s := by
    rw [convolve_comm H ρ, convolve_apply]
    simp_rw [zero_sub, show ∀ s, H (-s) = H s from H_even]
  have hi₁ : Integrable (fun s : ℝ => ρ s * H s) := by
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp H_isProfile.2.2.1
    exact hiρ.mul_bdd H_isProfile.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => hM (H s) ⟨s, rfl⟩)
  have hi₂ : Integrable (fun s : ℝ => (ρ s * ∫ u in (s - 1)..(s + 1), H u) / 2) := by
    have hi : Integrable (fun s : ℝ => ∫ u in Icc (-1 : ℝ) 1, ρ s * H (u - s)) :=
      hprod.integral_prod_right
    simp_rw [integral_const_mul, shifted_integral_H] at hi
    exact hi.div_const 2
  simp only [cumulant]
  rw [hzero, hsum, ← integral_div, ← integral_sub hi₁ hi₂, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hs.2] with s hz
  by_cases hm : s ∈ Icc (-1 : ℝ) 1
  · have h := extremalKernel_eq hm
    rw [extremalKernel] at h
    rw [show ρ s * H s - ρ s * (∫ u in (s - 1)..(s + 1), H u) / 2 =
      ρ s * (H s - (∫ u in (s - 1)..(s + 1), H u) / 2) by ring, h, mul_comm]
  · simp [hz hm]

theorem innerGG_eq_extremal_constant : innerGG = (Real.cot (1 / 4) - 3) / 8 := by
  rw [innerGG, extremal_cumulant H H_isProfile H_hasRadiusAtMost, integral_H, mul_one]

end Chowla
