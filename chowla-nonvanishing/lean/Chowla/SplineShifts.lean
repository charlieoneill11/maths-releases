import Chowla.Splines
import Chowla.Model.Symmetry

namespace Chowla

open Filter MeasureTheory Set
open scoped BigOperators

/-- The second difference associated with an odd rectangle. -/
noncomputable def shiftDifference (a : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * h x - h (x + a) - h (x - a)

private structure LowerInput (h : ℝ → ℝ) : Prop where
  integrableOn : ∀ x : ℝ, IntegrableOn h (Iic x)
  vanishesOnLeft : ∃ c : ℝ, ∀ x < c, h x = 0

private theorem lowerPrimitive_one_apply (h : ℝ → ℝ) (x : ℝ) :
    lowerPrimitive 1 h x = ∫ v in Iic x, h v := rfl

private theorem lowerPrimitive_succ_apply (n : ℕ) (h : ℝ → ℝ) (x : ℝ) :
    lowerPrimitive (n + 1) h x = ∫ v in Iic x, lowerPrimitive n h v := rfl

private theorem LowerInput.intervalIntegrable {h : ℝ → ℝ} (hh : LowerInput h) (a b : ℝ) :
    IntervalIntegrable h volume a b :=
  ⟨(hh.integrableOn b).mono_set fun _ hx => hx.2,
    (hh.integrableOn a).mono_set fun _ hx => hx.2⟩

private theorem LowerInput.primitive {h : ℝ → ℝ} (hh : LowerInput h) :
    LowerInput (lowerPrimitive 1 h) := by
  have hEq (x : ℝ) : lowerPrimitive 1 h x = lowerPrimitive 1 h 0 + ∫ v in (0 : ℝ)..x, h v := by
    rw [← intervalIntegral.integral_Iic_sub_Iic (hh.integrableOn 0) (hh.integrableOn x)]
    simp only [lowerPrimitive_one_apply]
    ring
  have hc : Continuous (lowerPrimitive 1 h) := by
    rw [show lowerPrimitive 1 h = fun x => lowerPrimitive 1 h 0 + ∫ v in (0 : ℝ)..x, h v from funext hEq]
    exact continuous_const.add (intervalIntegral.continuous_primitive hh.intervalIntegrable 0)
  obtain ⟨c, hcut⟩ := hh.vanishesOnLeft
  have hzero (x : ℝ) (hx : x < c) : lowerPrimitive 1 h x = 0 := by
    rw [lowerPrimitive_one_apply]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with v hv
    exact hcut v (lt_of_le_of_lt hv hx)
  have hsup : Function.support (lowerPrimitive 1 h) ⊆ Ici c := by
    rw [Function.support_subset_iff']
    intro x hx
    exact hzero x (lt_of_not_ge hx)
  refine ⟨fun x => ?_, c, hzero⟩
  apply (integrableOn_iff_integrable_of_support_subset hsup).1
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ici, Ici_inter_Iic]
  exact hc.integrableOn_Icc

private theorem LowerInput.iterate {h : ℝ → ℝ} (hh : LowerInput h) (n : ℕ) :
    LowerInput (lowerPrimitive n h) := by
  induction n with
  | zero => exact hh
  | succ n ih => exact ih.primitive

private theorem lowerInput_of_profile {h : ℝ → ℝ} (hh : IsProfile h) : LowerInput h := by
  refine ⟨fun _ => (integrable_of_isProfile hh).integrableOn, ?_⟩
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hh.2.2.2.isCompact.isBounded
  refine ⟨-C, fun x hx => ?_⟩
  by_contra hne
  have hs : x ∈ tsupport h := subset_closure hne
  have := hC x hs
  simp only [Real.norm_eq_abs] at this
  linarith [neg_le_abs x]

theorem integrableOn_lowerPrimitive {h : ℝ → ℝ} (hh : IsProfile h) (n : ℕ) (x : ℝ) :
    IntegrableOn (lowerPrimitive n h) (Iic x) :=
  ((lowerInput_of_profile hh).iterate n).integrableOn x

private theorem LowerInput.odd {h : ℝ → ℝ} (hh : LowerInput h) (hm : Measurable h) :
    LowerInput (oddProfile h) := by
  refine ⟨fun x => ?_, ?_⟩
  · exact Integrable.mono (hh.integrableOn x)
      ((measurable_oddProfile hm).aestronglyMeasurable)
      (Eventually.of_forall fun v => by
        simpa only [Real.norm_eq_abs] using abs_oddProfile_le h v)
  · obtain ⟨c, hc⟩ := hh.vanishesOnLeft
    exact ⟨c, fun x hx => by simp [oddProfile, hc x hx]⟩

private theorem lowerInput_shiftOn {h : ℝ → ℝ} (hh : LowerInput h) (a x : ℝ) :
    IntegrableOn (fun y => h (y + a)) (Iic x) := by
  have he : (Iic x).indicator (fun y => h (y + a)) =
      fun y => (Iic (x + a)).indicator h (y + a) := by
    funext y
    simp [indicator_apply]
  have hi := (hh.integrableOn (x + a)).integrable_indicator measurableSet_Iic
  have hia := hi.comp_add_right a
  rw [← he] at hia
  exact (integrable_indicator_iff measurableSet_Iic).mp hia

private theorem lowerPrimitive_translate (h : ℝ → ℝ) (a x : ℝ) :
    lowerPrimitive 1 (fun y => h (y + a)) x = lowerPrimitive 1 h (x + a) := by
  simp only [lowerPrimitive_one_apply, ← integral_indicator measurableSet_Iic]
  rw [← integral_add_right_eq_self ((Iic (x + a)).indicator h) a]
  congr 1
  funext y
  simp [indicator_apply]

private theorem LowerInput.shiftDifference {h : ℝ → ℝ} (hh : LowerInput h) (a : ℝ) :
    LowerInput (Chowla.shiftDifference a h) := by
  refine ⟨fun x => ?_, ?_⟩
  · have hp := lowerInput_shiftOn hh a x
    have hm := lowerInput_shiftOn hh (-a) x
    simpa only [Chowla.shiftDifference, sub_eq_add_neg] using
      (((hh.integrableOn x).const_mul 2).sub hp).sub hm
  · obtain ⟨c, hc⟩ := hh.vanishesOnLeft
    refine ⟨c - |a|, fun x hx => ?_⟩
    have h0 : x < c := by linarith [abs_nonneg a]
    have h1 : x + a < c := by linarith [le_abs_self a]
    have h2 : x - a < c := by linarith [neg_le_abs a]
    simp [Chowla.shiftDifference, hc x h0, hc (x+a) h1, hc (x-a) h2]

private theorem integral_sub_sub {f g k : ℝ → ℝ} {μ : Measure ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hk : Integrable k μ) :
    (∫ v, f v - g v - k v ∂μ) = (∫ v, f v ∂μ) - (∫ v, g v ∂μ) - ∫ v, k v ∂μ := by
  calc
    _ = (∫ v, f v - g v ∂μ) - ∫ v, k v ∂μ := by
      simpa only [Pi.sub_apply] using (integral_sub (hf.sub hg) hk)
    _ = _ := by rw [integral_sub hf hg]

private theorem lowerPrimitive_shiftDifference {h : ℝ → ℝ} (hh : LowerInput h) (a : ℝ) :
    lowerPrimitive 1 (shiftDifference a h) = shiftDifference a (lowerPrimitive 1 h) := by
  funext x
  have hp := lowerInput_shiftOn hh a x
  have hm : IntegrableOn (fun y => h (y - a)) (Iic x) := by
    simpa only [sub_eq_add_neg] using lowerInput_shiftOn hh (-a) x
  have hmul := (hh.integrableOn x).const_mul 2
  change (∫ v in Iic x, 2 * h v - h (v + a) - h (v - a)) =
    2 * lowerPrimitive 1 h x - lowerPrimitive 1 h (x + a) - lowerPrimitive 1 h (x - a)
  rw [integral_sub_sub hmul hp hm, integral_const_mul]
  change 2 * lowerPrimitive 1 h x - lowerPrimitive 1 (fun y => h (y + a)) x -
    lowerPrimitive 1 (fun y => h (y - a)) x = _
  rw [lowerPrimitive_translate h a x]
  simp only [sub_eq_add_neg]
  rw [lowerPrimitive_translate]

private theorem lowerPrimitive_iterate_shiftDifference {h : ℝ → ℝ}
    (hh : LowerInput h) (a : ℝ) (n : ℕ) :
    lowerPrimitive n (shiftDifference a h) = shiftDifference a (lowerPrimitive n h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change lowerPrimitive 1 (lowerPrimitive n (shiftDifference a h)) =
      shiftDifference a (lowerPrimitive 1 (lowerPrimitive n h))
    rw [ih, lowerPrimitive_shiftDifference (hh.iterate n)]

private theorem lowerPrimitive_iterate_one (h : ℝ → ℝ) (n : ℕ) :
    lowerPrimitive n (lowerPrimitive 1 h) = lowerPrimitive (n + 1) h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change lowerPrimitive 1 (lowerPrimitive n (lowerPrimitive 1 h)) =
      lowerPrimitive 1 (lowerPrimitive (n + 1) h)
    rw [ih]

private theorem odd_rect_abs_le_one (a t : ℝ) : |oddProfile (rectangle a) t| ≤ 1 := by
  exact (abs_oddProfile_le _ _).trans (by simp [rectangle, indicator_apply]; split <;> norm_num)

private theorem odd_rect_integrable (a : ℝ) : Integrable (oddProfile (rectangle a)) := by
  have hm : Measurable (rectangle a) := measurable_const.indicator measurableSet_Icc
  have hi : Integrable (rectangle a) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-a) a))
  exact integrable_oddProfile hm hi

private theorem rectangle_even_for_tail (a : ℝ) : Function.Even (rectangle a) := by
  intro v
  have hmem : -v ∈ Icc (-a) a ↔ v ∈ Icc (-a) a := by
    exact ⟨fun h => ⟨by linarith [h.2], by linarith [h.1]⟩,
      fun h => ⟨by linarith [h.2], by linarith [h.1]⟩⟩
  simp [rectangle, indicator_apply, hmem]

private theorem odd_rect_integral (a : ℝ) : (∫ v : ℝ, oddProfile (rectangle a) v) = 0 := by
  have he : ∀ v : ℝ, oddProfile (rectangle a) (-v) = -oddProfile (rectangle a) v := by
    intro v
    have hrect := rectangle_even_for_tail a v
    rcases lt_trichotomy v 0 with h | rfl | h
    · simp [oddProfile, h, hrect, (neg_pos.mpr h), (not_lt.mpr (neg_pos.mpr h).le)]
    · simp [oddProfile]
    · simp [oddProfile, h, hrect, (neg_neg_of_pos h), (not_lt.mpr h.le)]
  have hs : (∫ v : ℝ, oddProfile (rectangle a) v) = -(∫ v : ℝ, oddProfile (rectangle a) v) := by
    rw [← integral_neg]
    conv_lhs => rw [← integral_neg_eq_self]
    simp_rw [he]
  linarith

/-- Convolution with an odd rectangle is a three-point difference of the lower primitive. -/
theorem convolve_odd_rectangle {h : ℝ → ℝ} (hh : ∀ x : ℝ, IntegrableOn h (Iic x))
    (a : ℝ) (ha : 0 < a) :
    convolve h (oddProfile (rectangle a)) = shiftDifference a (lowerPrimitive 1 h) := by
  funext x
  let f (b : ℝ) := (Iic b).indicator h
  have hf (b : ℝ) : Integrable (f b) := (hh b).integrable_indicator measurableSet_Iic
  rw [convolve_apply]
  have hEq : (fun v : ℝ => h v * oddProfile (rectangle a) (x - v)) =ᵐ[volume]
      (fun v => 2 * f x v - f (x + a) v - f (x - a) v) := by
    filter_upwards [volume.ae_ne x, volume.ae_ne (x - a)] with v hv hv'
    by_cases h0 : v < x
    · have hpos : 0 < x - v := by linarith
      have hp : v ≤ x + a := by linarith
      by_cases hm : v < x - a
      · have hc : x - v ∉ Icc (-a) a := fun hm' => by linarith [hm'.2]
        simp [oddProfile, rectangle, hpos, hc, f, hp, h0.le, hm.le]
        ring
      · have hm' : x - a < v := lt_of_le_of_ne (le_of_not_gt hm) (Ne.symm hv')
        have hc : x - v ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
        simp [oddProfile, rectangle, hpos, not_lt.mpr hpos.le, hc, f, hp, h0.le, hm'.not_ge]
        ring
    · have h0' : x < v := lt_of_le_of_ne (le_of_not_gt h0) (Ne.symm hv)
      have hneg : x - v < 0 := by linarith
      have hm : ¬ v ≤ x - a := by linarith
      by_cases hp : v ≤ x + a
      · have hc : x - v ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
        simp [oddProfile, rectangle, hneg, hc, f, hp, h0'.not_ge, hm]
      · have hc : x - v ∉ Icc (-a) a := fun hc' => hp (by linarith [hc'.1])
        simp [oddProfile, rectangle, hneg, hc, f, hp, h0'.not_ge, hm]
  rw [integral_congr_ae hEq, integral_sub_sub ((hf x).const_mul 2) (hf (x + a)) (hf (x - a)),
    integral_const_mul]
  simp only [f, integral_indicator measurableSet_Iic, shiftDifference, lowerPrimitive_one_apply]

private noncomputable def convolutionRects (h : ℝ → ℝ) (A : List ℝ) : ℝ → ℝ :=
  convolutionList (h :: A.map (fun a => oddProfile (rectangle a)))

private theorem integrable_convolutionRects {h : ℝ → ℝ} (hh : Integrable h) (A : List ℝ) :
    Integrable (convolutionRects h A) := by
  apply convolutionList_integrable
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hh
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
    exact odd_rect_integrable a

private theorem convolutionRects_cons {h : ℝ → ℝ} (hh : Integrable h) (a : ℝ) (A : List ℝ) :
    convolutionRects h (a :: A) = convolve (convolutionRects h A) (oddProfile (rectangle a)) := by
  cases A with
  | nil => rfl
  | cons b B =>
    let tail := convolutionList ((b :: B).map (fun a => oddProfile (rectangle a)))
    have ht : Integrable tail := integrable_convolutionRects (odd_rect_integrable b) B
    change convolve h (convolve (oddProfile (rectangle a)) tail) =
      convolve (convolve h tail) (oddProfile (rectangle a))
    rw [convolve_comm (oddProfile (rectangle a)) tail,
      convolve_assoc_of_bound hh ht (odd_rect_integrable a) (odd_rect_abs_le_one a)]

private theorem lowerInput_convolutionRects {h : ℝ → ℝ} (hh : Integrable h) (hl : LowerInput h)
    (A : List ℝ) (ha : ∀ a ∈ A, 0 < a) : LowerInput (convolutionRects h A) := by
  induction A with
  | nil => exact hl
  | cons a A ih =>
    have htail := ih (fun a ha' => ha a (List.mem_cons_of_mem _ ha'))
    rw [convolutionRects_cons hh, convolve_odd_rectangle htail.integrableOn a (ha a (by simp))]
    exact htail.primitive.shiftDifference a

private theorem lowerPrimitive_convolutionRects {h : ℝ → ℝ} (hh : Integrable h)
    (hl : LowerInput h) (n : ℕ) (A : List ℝ) (ha : ∀ a ∈ A, 0 < a) :
    lowerPrimitive n (convolutionRects h A) =
      A.foldr shiftDifference (lowerPrimitive (n + A.length) h) := by
  induction A generalizing n with
  | nil => rfl
  | cons a A ih =>
    have ha' : ∀ b ∈ A, 0 < b := fun b hb => ha b (List.mem_cons_of_mem _ hb)
    have htail := lowerInput_convolutionRects hh hl A ha'
    rw [convolutionRects_cons hh, convolve_odd_rectangle htail.integrableOn a (ha a (by simp)),
      lowerPrimitive_iterate_shiftDifference htail.primitive, lowerPrimitive_iterate_one, ih]
    · rw [List.foldr_cons, List.length_cons]
      rw [show n + 1 + A.length = n + (A.length + 1) by omega]
    · exact ha'

/-- The convolution tail for any nonempty list of odd rectangles is the negative of the
corresponding finite difference of a lower primitive. -/
theorem odd_rectangle_tail (h : ℝ → ℝ) (hh : IsProfile h) (A : List ℝ)
    (ha : ∀ a ∈ A, 0 < a) (hn : A ≠ []) :
    (∫ u in Ioi (1 : ℝ), convolutionList ((h :: A.map rectangle).map oddProfile) u) =
      -((A.foldr shiftDifference (lowerPrimitive (A.length + 1) (oddProfile h))) 1) := by
  have ho := integrable_oddProfile hh.1 (integrable_of_isProfile hh)
  have hol := (lowerInput_of_profile hh).odd hh.1
  have hI := integrable_convolutionRects ho A
  have hsum : (∫ u : ℝ, convolutionRects (oddProfile h) A u) = 0 := by
    cases A with
    | nil => exact (hn rfl).elim
    | cons a A =>
      rw [convolutionRects_cons ho, integral_convolve (integrable_convolutionRects ho A)
        (odd_rect_integrable a), odd_rect_integral, mul_zero]
  have hs := intervalIntegral.integral_Iic_add_Ioi (b := (1 : ℝ)) hI.integrableOn hI.integrableOn
  have he := congrFun (lowerPrimitive_convolutionRects ho hol 1 A ha) 1
  rw [lowerPrimitive_one_apply, Nat.add_comm 1 A.length] at he
  rw [hsum] at hs
  simp only [List.map_cons, List.map_map]
  change (∫ u in Ioi (1 : ℝ), convolutionRects (oddProfile h) A u) = _
  linarith

/-- Lemma 28, before expressing the odd primitive through the even profile's primitives. -/
theorem cumulant_shift (h : ℝ → ℝ) (hh : IsProfile h) (A : List ℝ)
    (hA : ∀ a ∈ A, a ∈ Ioc (0 : ℝ) 1) (hlen : 2 ≤ A.length) :
    cumulant (h :: A.map rectangle) =
      (-2 : ℝ) ^ (A.length + 1) / 2 *
        (A.foldr shiftDifference (lowerPrimitive (A.length + 1) (oddProfile h))) 1 := by
  have he : cumulant (h :: A.map rectangle) = delta (h :: A.map rectangle) := by
    cases A with
    | nil => simp at hlen
    | cons a A =>
      cases A with
      | nil => simp at hlen
      | cons b A => rfl
  rw [he, delta, odd_rectangle_tail h hh A (fun a ha => (hA a ha).1)]
  · simp only [List.length_cons, List.length_map]
    ring
  · intro he
    simp [he] at hlen

private theorem lowerPrimitive_odd_nonpos (h : ℝ → ℝ) (n : ℕ) (x : ℝ) (hx : x ≤ 0) :
    lowerPrimitive (n + 1) (oddProfile h) x = -lowerPrimitive (n + 1) h x := by
  induction n generalizing x with
  | zero =>
    change (∫ v in Iic x, oddProfile h v) = -(∫ v in Iic x, h v)
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic,
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne (0 : ℝ))] with v hv hne
    exact if_pos (lt_of_le_of_ne (hv.trans hx) hne)
  | succ n ih =>
    rw [lowerPrimitive_succ_apply, lowerPrimitive_succ_apply, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Iic
    intro v hv
    exact ih v (hv.trans hx)

private theorem integral_pow_factorial (k : ℕ) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, t ^ k / k.factorial) = x ^ (k + 1) / (k + 1).factorial := by
  rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, div_div]

private theorem lowerPrimitive_add_interval {h : ℝ → ℝ} (hh : LowerInput h) (n : ℕ) (x : ℝ) :
    lowerPrimitive (n + 1) h x = lowerPrimitive (n + 1) h 0 +
      ∫ t in (0 : ℝ)..x, lowerPrimitive n h t := by
  rw [← intervalIntegral.integral_Iic_sub_Iic ((hh.iterate n).integrableOn 0)
    ((hh.iterate n).integrableOn x)]
  simp only [lowerPrimitive_succ_apply]
  ring

private theorem lowerPrimitive_odd_nonneg (h : ℝ → ℝ) (hh : IsProfile h) (n : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    lowerPrimitive (n + 1) (oddProfile h) x = lowerPrimitive (n + 1) h x -
      2 * ∑ k ∈ Finset.range (n + 1), x ^ k / k.factorial * lowerPrimitive (n + 1 - k) h 0 := by
  have hl := lowerInput_of_profile hh
  have ho := hl.odd hh.1
  induction n generalizing x with
  | zero =>
    have he : (∫ t in (0 : ℝ)..x, oddProfile h t) = ∫ t in (0 : ℝ)..x, h t := by
      rw [intervalIntegral.integral_of_le hx, intervalIntegral.integral_of_le hx]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp [oddProfile, ht.1, not_lt.mpr ht.1.le]
    rw [lowerPrimitive_add_interval ho 0 x, lowerPrimitive_odd_nonpos h 0 0 le_rfl,
      lowerPrimitive_add_interval hl 0 x]
    simp only [lowerPrimitive, Nat.zero_add, he, Finset.sum_range_one, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    ring
  | succ n ih =>
    let q (k : ℕ) (t : ℝ) := t ^ k / (k.factorial : ℝ) * lowerPrimitive (n + 1 - k) h 0
    have hq (k : ℕ) : Continuous (q k) := by unfold q; fun_prop
    have hsum : Continuous (fun t => ∑ k ∈ Finset.range (n + 1), q k t) :=
      continuous_finset_sum _ fun k _ => hq k
    have hEq : (∫ t in (0 : ℝ)..x, lowerPrimitive (n + 1) (oddProfile h) t) =
        ∫ t in (0 : ℝ)..x, lowerPrimitive (n + 1) h t -
          2 * ∑ k ∈ Finset.range (n + 1), q k t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx] at ht
      exact ih t ht.1
    have hInt :
        (∫ t in (0 : ℝ)..x, ∑ k ∈ Finset.range (n + 1), q k t) =
        ∑ k ∈ Finset.range (n + 1), x ^ (k + 1) / (k + 1).factorial *
          lowerPrimitive (n + 1 - k) h 0 := by
      rw [intervalIntegral.integral_finset_sum (fun k _ => (hq k).intervalIntegrable 0 x)]
      apply Finset.sum_congr rfl
      intro k _
      change (∫ t in (0 : ℝ)..x, t ^ k / (k.factorial : ℝ) * lowerPrimitive (n + 1 - k) h 0) = _
      rw [intervalIntegral.integral_mul_const, integral_pow_factorial]
    have hSumShift :
        (∑ k ∈ Finset.range (n + 1 + 1),
            x ^ k / k.factorial * lowerPrimitive (n + 1 + 1 - k) h 0) =
          (∑ k ∈ Finset.range (n + 1),
            x ^ (k + 1) / (k + 1).factorial * lowerPrimitive (n + 1 - k) h 0) +
            lowerPrimitive (n + 1 + 1) h 0 := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, pow_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, one_mul, Nat.sub_zero]
    rw [lowerPrimitive_add_interval ho (n + 1),
      lowerPrimitive_odd_nonpos h (n + 1) 0 le_rfl, hEq,
      intervalIntegral.integral_sub ((hl.iterate (n + 1)).intervalIntegrable 0 x)
        ((hsum.const_mul 2).intervalIntegrable 0 x), intervalIntegral.integral_const_mul,
      hInt, hSumShift]
    conv_rhs => rw [lowerPrimitive_add_interval hl (n + 1)]
    ring

/-- The signed lower primitive of Lemma 28, in terms of the primitive values at zero. -/
theorem lowerPrimitive_oddProfile (h : ℝ → ℝ) (hh : IsProfile h) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    lowerPrimitive n (oddProfile h) x =
      if x < 0 then -lowerPrimitive n h x else
        lowerPrimitive n h x -
          2 * ∑ k ∈ Finset.range n, x ^ k / k.factorial * lowerPrimitive (n - k) h 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  by_cases hx : x < 0
  · rw [if_pos hx]
    exact lowerPrimitive_odd_nonpos h n x hx.le
  · rw [if_neg hx]
    exact lowerPrimitive_odd_nonneg h hh n x (le_of_not_gt hx)

private theorem rectangle_profile_for_tail (a : ℝ) : IsProfile (rectangle a) := by
  refine ⟨measurable_const.indicator measurableSet_Icc, rectangle_even_for_tail a, ?_, ?_⟩
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [Real.norm_eq_abs]
    by_cases hu : u ∈ Icc (-a) a <;> simp [rectangle, hu]
  · exact HasCompactSupport.intro (K := Icc (-a) a) isCompact_Icc fun x hx => by simp [rectangle, hx]

private theorem odd_rectangle_ae_shift_zero (a : ℝ) (ha : 0 < a) :
    oddProfile (rectangle a) =ᵐ[volume] shiftDifference a (truncatedPower 0 0) := by
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne a] with x hx hxa
  rcases lt_or_gt_of_ne hx with hn | hp
  · have h1 : x ≤ a := by linarith
    have h2 : ¬ 0 ≤ x - a := by linarith
    by_cases h3 : -a ≤ x
    · have h4 : 0 ≤ x + a := by linarith
      simp [oddProfile, rectangle, show x ∈ Icc (-a) a from ⟨h3, h1⟩, hn,
        hn.not_ge, shiftDifference, truncatedPower, h2, h4]
    · have h4 : ¬ 0 ≤ x + a := by linarith
      have hmem : x ∉ Icc (-a) a := fun h => h3 h.1
      simp [oddProfile, rectangle, hn, hmem, hn.not_ge, shiftDifference, truncatedPower, h2, h4]
  · have h1 : -a ≤ x := by linarith
    have h2 : 0 ≤ x + a := by linarith
    by_cases h3 : x < a
    · have h4 : ¬ 0 ≤ x - a := by linarith
      simp [oddProfile, rectangle, show x ∈ Icc (-a) a from ⟨h1, h3.le⟩, hp,
        hp.not_gt, shiftDifference, truncatedPower, h2, h4, hp.le]
      norm_num
    · have h4 : 0 ≤ x - a := by linarith
      have hmem : x ∉ Icc (-a) a := fun h => hxa (le_antisymm h.2 (le_of_not_gt h3))
      simp [oddProfile, rectangle, hp, hp.not_gt, hp.le, hmem, shiftDifference,
        truncatedPower, h2, h4]
      norm_num

private theorem lowerPrimitive_congr_ae {f g : ℝ → ℝ} (hle : f =ᵐ[volume] g) (n : ℕ) :
    lowerPrimitive (n + 1) f = lowerPrimitive (n + 1) g := by
  induction n with
  | zero =>
    funext x
    exact integral_congr_ae (ae_restrict_of_ae hle)
  | succ n ih =>
    change lowerPrimitive 1 (lowerPrimitive (n + 1) f) =
      lowerPrimitive 1 (lowerPrimitive (n + 1) g)
    rw [ih]

private theorem lowerPrimitive_truncatedPower_at_zero (n : ℕ) :
    lowerPrimitive n (truncatedPower 0 0) = truncatedPower 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change lowerPrimitive 1 (lowerPrimitive n (truncatedPower 0 0)) = _
    rw [ih, integral_truncatedPower]

private theorem shiftDifference_comm (a b : ℝ) (f : ℝ → ℝ) :
    shiftDifference a (shiftDifference b f) = shiftDifference b (shiftDifference a f) := by
  funext x
  simp only [shiftDifference]
  rw [show x + a + b = x + b + a by ring,
    show x + a - b = x - b + a by ring,
    show x - a + b = x + b - a by ring,
    show x - a - b = x - b - a by ring]
  ring

private theorem shiftDifference_foldr_comm (a : ℝ) (A : List ℝ) (f : ℝ → ℝ) :
    A.foldr shiftDifference (shiftDifference a f) =
      shiftDifference a (A.foldr shiftDifference f) := by
  induction A with
  | nil => rfl
  | cons b A ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, shiftDifference_comm b a]

/-- The unmarked rectangle tail in Lemma 25, given by the shift formula for one step
at zero and one finite difference for each width. -/
theorem delta_rectangles_shift (A : List ℝ) (hA : ∀ a ∈ A, 0 < a) (hlen : 2 ≤ A.length) :
    delta (A.map rectangle) =
      (-2 : ℝ) ^ A.length / 2 *
        (A.foldr shiftDifference (fun x => (max x 0) ^ A.length / A.length.factorial)) 1 := by
  cases A with
  | nil => simp at hlen
  | cons a A =>
    have hapos : 0 < a := hA a (by simp)
    have hA' : ∀ b ∈ A, 0 < b := fun b hb => hA b (List.mem_cons_of_mem _ hb)
    have hne : A ≠ [] := fun h => by simp [h] at hlen
    have hbase : LowerInput (truncatedPower 0 0) :=
      ⟨truncatedPower_integrableOn 0 0, 0, fun x hx => by simp [truncatedPower, hx.not_ge]⟩
    have hpr :
        lowerPrimitive (A.length + 1) (oddProfile (rectangle a)) =
          shiftDifference a (truncatedPower 0 (A.length + 1)) := by
      rw [lowerPrimitive_congr_ae (odd_rectangle_ae_shift_zero a hapos),
        lowerPrimitive_iterate_shiftDifference hbase, lowerPrimitive_truncatedPower_at_zero]
    have hpower : truncatedPower 0 (A.length + 1) =
        fun x : ℝ => (max x 0) ^ (A.length + 1) / (A.length + 1).factorial := by
      funext x
      by_cases hx : 0 ≤ x
      · simp [truncatedPower, hx]
      · simp [truncatedPower, hx, max_eq_right (le_of_not_ge hx), zero_pow (Nat.succ_ne_zero _)]
    rw [delta, List.map_cons, odd_rectangle_tail (rectangle a) (rectangle_profile_for_tail a) A hA' hne,
      hpr, shiftDifference_foldr_comm, hpower]
    simp only [List.length_cons, List.length_map, List.foldr_cons]
    ring

end Chowla
