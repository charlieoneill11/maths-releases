import Chowla.SplineShifts

namespace Chowla

open Filter MeasureTheory Set
open scoped BigOperators

/-- The definite integral in the mean and covariance formulas, as a primitive difference. -/
theorem definite_eq_lowerPrimitive_sub {h : ℝ → ℝ} (hh : Integrable h) (l r : ℝ) :
    (∫ u in l..r, h u) = lowerPrimitive 1 h r - lowerPrimitive 1 h l :=
  (intervalIntegral.integral_Iic_sub_Iic hh.integrableOn hh.integrableOn).symm

/-- Integrating the one-fold primitive above its value at the left endpoint adds
a linear factor in the integrand. -/
private theorem integral_lowerPrimitive_sub {h : ℝ → ℝ} (hh : Integrable h) {l r : ℝ} (hlr : l ≤ r) :
    (∫ t in l..r, lowerPrimitive 1 h t - lowerPrimitive 1 h l) =
      ∫ t in l..r, (r - t) * h t := by
  rw [intervalIntegral.integral_of_le hlr, intervalIntegral.integral_of_le hlr]
  let μ := (volume : Measure ℝ).restrict (Ioc l r)
  let F := fun x y : ℝ => (Iic x).indicator h y
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hF : Integrable (Function.uncurry F) (μ.prod μ) := by
    let s : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}
    have hs : MeasurableSet s := measurableSet_le measurable_snd measurable_fst
    have hm : Integrable h μ := hh.integrableOn
    exact (hm.comp_snd μ).indicator hs
  have hleft : (∫ t in Ioc l r, lowerPrimitive 1 h t - lowerPrimitive 1 h l) =
      ∫ x, ∫ y, F x y ∂μ ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    change lowerPrimitive 1 h x - lowerPrimitive 1 h l = ∫ y, F x y ∂μ
    rw [← definite_eq_lowerPrimitive_sub hh, intervalIntegral.integral_of_le hx.1.le]
    change (∫ t in Ioc l x, h t) = ∫ y, (Iic x).indicator h y ∂μ
    rw [integral_indicator measurableSet_Iic, show μ = volume.restrict (Ioc l r) from rfl,
      Measure.restrict_restrict measurableSet_Iic]
    have he : Ioc l x = Iic x ∩ Ioc l r := by
      apply Set.ext
      intro y
      exact ⟨fun hy => ⟨hy.2, hy.1, hy.2.trans hx.2⟩, fun hy => ⟨hy.2.1, hy.1⟩⟩
    rw [he]
  rw [hleft, integral_integral_swap hF]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  change (∫ x, F x y ∂μ) = (r-y) * h y
  have hyf : (fun x => F x y) = (Ici y).indicator (fun _ => h y) := by
    funext x
    rfl
  rw [hyf, integral_indicator measurableSet_Ici, show μ = volume.restrict (Ioc l r) from rfl,
    Measure.restrict_restrict measurableSet_Ici]
  have hyS : Ici y ∩ Ioc l r = Icc y r := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hy.1.trans_le hx.1, hx.2⟩⟩
  rw [hyS, setIntegral_const, Real.volume_real_Icc_of_le hy.2, smul_eq_mul]

private theorem second_primitive_linear {h : ℝ → ℝ} (hh : IsProfile h) {l r : ℝ} (hle : l ≤ r) :
    lowerPrimitive 2 h r - lowerPrimitive 2 h l - (r - l) * lowerPrimitive 1 h l =
      ∫ t in l..r, (r - t) * h t := by
  have h1 (x : ℝ) := integrableOn_lowerPrimitive hh 1 x
  have hi : IntervalIntegrable (lowerPrimitive 1 h) volume l r :=
    ⟨(h1 r).mono_set fun _ hx => hx.2, (h1 l).mono_set fun _ hx => hx.2⟩
  have hdiff := integral_lowerPrimitive_sub (integrable_of_isProfile hh) hle
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const] at hdiff
  rw [← hdiff]
  have hd := intervalIntegral.integral_Iic_sub_Iic (h1 l) (h1 r)
  change lowerPrimitive 2 h r - lowerPrimitive 2 h l = _ at hd
  rw [hd, smul_eq_mul]

private theorem intervalWeighted_integrable {h : ℝ → ℝ} (hh : Integrable h) {l r : ℝ}
    {f : ℝ → ℝ} (hf : Continuous f) : IntervalIntegrable (fun x => f x * h x) volume l r := by
  have h' := (hh.intervalIntegrable (a := l) (b := r)).mul_continuousOn hf.continuousOn
  simpa only [mul_comm] using h'

theorem weighted_integral_eq_primitives {h : ℝ → ℝ} (hh : IsProfile h) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, u * h u) =
      t * lowerPrimitive 1 h t - lowerPrimitive 2 h t + lowerPrimitive 2 h 0 := by
  have hi := integrable_of_isProfile hh
  have hs := second_primitive_linear hh ht
  have he : (∫ u in (0 : ℝ)..t, (t - u) * h u) =
      t * (∫ u in (0 : ℝ)..t, h u) - ∫ u in (0 : ℝ)..t, u * h u := by
    simp only [sub_mul]
    have h1 : IntervalIntegrable (fun u => t * h u) volume 0 t :=
      intervalWeighted_integrable hi continuous_const
    have h2 : IntervalIntegrable (fun u => u * h u) volume 0 t :=
      intervalWeighted_integrable hi continuous_id
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  rw [he, definite_eq_lowerPrimitive_sub hi] at hs
  linarith

private theorem integral_gamma {h : ℝ → ℝ} (hh : IsProfile h) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u : ℝ, |u| * h u * rectangle t u) = 2 * ∫ u in (0 : ℝ)..t, u * h u := by
  have hi := integrable_of_isProfile hh
  have he : (fun u : ℝ => |u| * h u * rectangle t u) =
      (Icc (-t) t).indicator (fun u => |u| * h u) := by
    funext u
    by_cases hu : u ∈ Icc (-t) t <;> simp [rectangle, hu]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -t ≤ t),
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalWeighted_integrable hi continuous_abs) (intervalWeighted_integrable hi continuous_abs)]
  have heven : ∀ x, h (-x) = h x := hh.2.1
  have hneg : (∫ x in (-t)..(0 : ℝ), |x| * h x) = ∫ x in (0 : ℝ)..t, |x| * h x := by
    simpa only [abs_neg, heven, neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -t) (b := 0) (fun x => |x| * h x))
  rw [hneg, ← two_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le ht] at hx
  change |x| * h x = x * h x
  rw [abs_of_nonneg hx.1]

private theorem odd_second_primitive_difference {h : ℝ → ℝ} (hh : IsProfile h)
    {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    shiftDifference a (lowerPrimitive 2 (oddProfile h)) 1 =
      shiftDifference a (lowerPrimitive 2 h) 1 := by
  have hb : 0 ≤ 1 + a := by linarith [ha.1]
  have hc : 0 ≤ 1 - a := by linarith [ha.2]
  simp only [shiftDifference]
  rw [lowerPrimitive_oddProfile h hh 2 (by decide) 1,
    lowerPrimitive_oddProfile h hh 2 (by decide) (1 + a),
    lowerPrimitive_oddProfile h hh 2 (by decide) (1 - a)]
  norm_num [not_lt.mpr hb, not_lt.mpr hc, Finset.sum_range_succ]
  ring

/-- Lemma 27 with the definite integrals expressed by the first two lower primitives. -/
theorem cumulant_covariance_primitives {h : ℝ → ℝ} (hh : IsProfile h)
    {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    cumulant [h, rectangle a] =
      4 * (a * lowerPrimitive 1 h a - lowerPrimitive 2 h a + lowerPrimitive 2 h 0) -
      2 * (lowerPrimitive 2 h (1 + a) - 2 * lowerPrimitive 2 h 1 + lowerPrimitive 2 h (1 - a)) := by
  have hd := odd_rectangle_tail h hh [a] (by simpa using ha.1) (by simp)
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.foldr_cons,
    List.foldr_nil] at hd
  change (∫ u in Ioi (1 : ℝ), convolutionList (([h, rectangle a]).map oddProfile) u) =
    -shiftDifference a (lowerPrimitive 2 (oddProfile h)) 1 at hd
  change 2 * (∫ u : ℝ, |u| * h u * rectangle a u) + delta [h, rectangle a] = _
  rw [integral_gamma hh ha.1.le, weighted_integral_eq_primitives hh ha.1.le, delta, hd,
    odd_second_primitive_difference hh ha, shiftDifference]
  norm_num
  ring

theorem triangular_integral_eq_primitives {h : ℝ → ℝ} (hh : IsProfile h)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ u in (1 - a)..(1 + a), (a - |1 - u|) * h u) =
      lowerPrimitive 2 h (1 + a) - 2 * lowerPrimitive 2 h 1 +
        lowerPrimitive 2 h (1 - a) := by
  have hi := integrable_of_isProfile hh
  have hleft : 1 - a ≤ (1 : ℝ) := by linarith
  have hright : (1 : ℝ) ≤ 1 + a := by linarith
  have hcont : Continuous (fun u : ℝ => a - |1 - u|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalWeighted_integrable hi hcont) (intervalWeighted_integrable hi hcont)]
  have hl : (∫ u in (1 - a)..(1 : ℝ), (a - |1 - u|) * h u) =
      ∫ u in (1 - a)..(1 : ℝ), (a * h u - (1 - u) * h u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hleft] at hu
    change (a - |1 - u|) * h u = _
    rw [abs_of_nonneg (sub_nonneg.mpr hu.2), sub_mul]
  have hr : (∫ u in (1 : ℝ)..(1 + a), (a - |1 - u|) * h u) =
      ∫ u in (1 : ℝ)..(1 + a), (1 + a - u) * h u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hright] at hu
    change (a - |1 - u|) * h u = _
    rw [abs_of_nonpos (sub_nonpos.mpr hu.1)]
    ring
  have hi1 : IntervalIntegrable (fun u => a * h u) volume (1 - a) 1 :=
    intervalWeighted_integrable hi continuous_const
  have hi2 : IntervalIntegrable (fun u => (1 - u) * h u) volume (1 - a) 1 :=
    intervalWeighted_integrable hi (by fun_prop)
  rw [hl, hr, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    definite_eq_lowerPrimitive_sub hi, ← second_primitive_linear hh hleft,
    ← second_primitive_linear hh hright]
  ring

/-- Lemma 27, with the covariance written as its two definite integrals. -/
theorem cumulant_covariance (h : ℝ → ℝ) (hh : IsProfile h) (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    cumulant [h, rectangle t] =
      (4 * ∫ u in (0 : ℝ)..t, u * h u) -
      (2 * ∫ u in (1 - t)..(1 + t), (t - |1 - u|) * h u) := by
  rw [cumulant_covariance_primitives hh ht, weighted_integral_eq_primitives hh ht.1.le,
    triangular_integral_eq_primitives hh ht.1.le]

end Chowla
