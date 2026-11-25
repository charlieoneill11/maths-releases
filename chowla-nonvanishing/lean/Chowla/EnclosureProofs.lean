import Chowla.Enclosure
import Chowla.Model.Extremal
import Chowla.SplineCovariance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Chowla

open Filter MeasureTheory Set
open scoped Topology

theorem IsProfile.sub {f g : FourierProfile} (hf : IsProfile f) (hg : IsProfile g) :
    IsProfile (f - g) := by
  refine ⟨hf.1.sub hg.1, ?_, ?_, hf.2.2.2.sub hg.2.2.2⟩
  · intro x
    simp only [Pi.sub_apply, hf.2.1 x, hg.2.1 x]
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hf.2.2.1
    obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp hg.2.2.1
    refine isBounded_iff_forall_norm_le.mpr ⟨C + D, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (norm_sub_le (f x) (g x)).trans (add_le_add (hC _ ⟨x, rfl⟩) (hD _ ⟨x, rfl⟩))

theorem IsProfile.neg {f : FourierProfile} (hf : IsProfile f) : IsProfile (-f) := by
  refine ⟨hf.1.neg, fun u => by simp only [Pi.neg_apply, hf.2.1 u], ?_, hf.2.2.2.neg⟩
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hf.2.2.1
  refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
  rintro _ ⟨u, rfl⟩
  simpa only [Pi.neg_apply, norm_neg] using hC (f u) ⟨u, rfl⟩

theorem IsProfile.add {f g : FourierProfile} (hf : IsProfile f) (hg : IsProfile g) :
    IsProfile (f + g) := by simpa only [sub_neg_eq_add] using hf.sub hg.neg


theorem oddProfile_sub (f g : FourierProfile) : oddProfile (f - g) = oddProfile f - oddProfile g := by
  funext x
  simp only [oddProfile, Pi.sub_apply]
  split_ifs <;> ring

private theorem integrable_mul_shift {f g : FourierProfile} (hf : Integrable f) (hg : Measurable g)
    {C : ℝ} (hC : ∀ t, |g t| ≤ C) (u : ℝ) :
    Integrable (fun t => f t * g (u - t)) := by
  apply (hf.abs.mul_const C).mono'
      (hf.aestronglyMeasurable.mul (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  filter_upwards with t
  simp only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, id_eq, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC (u - t)) (abs_nonneg _)

private theorem convolve_sub_right {f g h : FourierProfile} (hf : Integrable f)
    (hg : Measurable g) (hh : Measurable h)
    {C D : ℝ} (hC : ∀ t, |g t| ≤ C) (hD : ∀ t, |h t| ≤ D) :
    convolve f (g - h) = convolve f g - convolve f h := by
  funext u
  simp only [convolve_apply, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_mul_shift hf hg hC u) (integrable_mul_shift hf hh hD u)

theorem convolve_sub_head {f g h : FourierProfile} (hf : IsProfile f) (hg : IsProfile g)
    (hh : Integrable h) : convolve (f - g) h = convolve f h - convolve g h := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hf.2.2.1
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp hg.2.2.1
  rw [convolve_comm (f - g), convolve_comm f, convolve_comm g]
  exact convolve_sub_right hh hf.1 hg.1
    (fun t => by simpa only [Real.norm_eq_abs] using hC (f t) ⟨t, rfl⟩)
    (fun t => by simpa only [Real.norm_eq_abs] using hD (g t) ⟨t, rfl⟩)

theorem convolve_add_head {f g h : FourierProfile} (hf : IsProfile f) (hg : IsProfile g)
    (hh : Integrable h) : convolve (f + g) h = convolve f h + convolve g h := by
  have H := convolve_sub_head (hf.add hg) hg hh
  rw [add_sub_cancel_right] at H
  exact (eq_sub_iff_add_eq.mp H).symm


private theorem convolutionList_odd_integrable {gs : List FourierProfile}
    (hgs : ∀ g ∈ gs, IsProfile g) : Integrable (convolutionList (gs.map oddProfile)) := by
  apply convolutionList_integrable
  intro h hh
  obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hh
  exact integrable_oddProfile (hgs g hmem).1 (integrable_of_isProfile (hgs g hmem))

private theorem delta_sub_head {f g : FourierProfile} (hf : IsProfile f) (hg : IsProfile g)
    (hs : List FourierProfile) (hhs : ∀ h ∈ hs, IsProfile h) :
    delta ((f - g) :: hs) = delta (f :: hs) - delta (g :: hs) := by
  have hlin :
      convolutionList ((((f - g) :: hs).map oddProfile)) =
        convolutionList ((f :: hs).map oddProfile) -
          convolutionList ((g :: hs).map oddProfile) := by
    rw [List.map_cons, oddProfile_sub]
    cases hs with
    | nil => simp [convolutionList]
    | cons a rest =>
      simp only [List.map_cons, convolutionList]
      have hint := convolutionList_odd_integrable hhs
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hf.2.2.1
      obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp hg.2.2.1
      rw [convolve_comm (oddProfile f - oddProfile g), convolve_comm (oddProfile f),
        convolve_comm (oddProfile g)]
      exact convolve_sub_right hint (measurable_oddProfile hf.1) (measurable_oddProfile hg.1)
        (fun t => (abs_oddProfile_le f t).trans (by simpa only [Real.norm_eq_abs] using hC (f t) ⟨t, rfl⟩))
        (fun t => (abs_oddProfile_le g t).trans (by simpa only [Real.norm_eq_abs] using hD (g t) ⟨t, rfl⟩))
  unfold delta
  simp only [List.length_cons]
  rw [hlin]
  change -((-2 : ℝ) ^ (hs.length + 1)) / 2 *
      (∫ u in Ioi (1 : ℝ), convolutionList ((f :: hs).map oddProfile) u -
        convolutionList ((g :: hs).map oddProfile) u) = _
  rw [integral_sub (convolutionList_odd_integrable (fun t ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hf
    · exact hhs t ht)).integrableOn (convolutionList_odd_integrable (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hg
      · exact hhs t ht)).integrableOn]
  ring

private theorem gaussian_integrable {f g : FourierProfile} (hf : IsProfile f) (hg : IsProfile g) :
    Integrable (fun u : ℝ => |u| * f u * g u) := by
  let K := tsupport g
  have hK : IsCompact K := hg.2.2.2.isCompact
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hf.2.2.1
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp hg.2.2.1
  have hB' : 0 ≤ max 0 B := le_max_left ..
  have hC' : 0 ≤ C := (norm_nonneg (f 0)).trans (hC (f 0) ⟨0, rfl⟩)
  have hsup : Function.support (fun u : ℝ => |u| * f u * g u) ⊆ K := by
    intro u hu
    apply subset_closure
    exact fun h => hu (by simp [h])
  apply (integrableOn_iff_integrable_of_support_subset hsup).mp
  refine Measure.integrableOn_of_bounded (M := max 0 B * C * D) hK.measure_ne_top
    ((continuous_abs.measurable.mul hf.1).mul hg.1).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
  simp only [Real.norm_eq_abs, abs_mul, abs_abs]
  exact mul_le_mul (mul_le_mul (by simpa only [Real.norm_eq_abs] using (hB u hu).trans (le_max_right 0 B))
    (by simpa only [Real.norm_eq_abs] using hC (f u) ⟨u, rfl⟩) (abs_nonneg _) hB')
    (by simpa only [Real.norm_eq_abs] using hD (g u) ⟨u, rfl⟩)
    (abs_nonneg _) (mul_nonneg hB' hC')

/-- Subtraction in the marked profile may be moved outside a restricted cumulant. -/
theorem cumulant_sub_head {f g : FourierProfile} (hf : IsProfile f) (hg : IsProfile g)
    (hs : List FourierProfile) (hhs : ∀ h ∈ hs, IsProfile h) :
    cumulant ((f - g) :: hs) = cumulant (f :: hs) - cumulant (g :: hs) := by
  cases hs with
  | nil =>
    simp only [cumulant, Pi.sub_apply]
    rw [intervalIntegral.integral_sub (integrable_of_isProfile hf).intervalIntegrable
      (integrable_of_isProfile hg).intervalIntegrable]
    ring
  | cons a rest =>
    cases rest with
    | nil =>
      have ha := hhs a (by simp)
      simp only [cumulant, Pi.sub_apply]
      simp only [mul_sub, sub_mul]
      rw [integral_sub (gaussian_integrable hf ha) (gaussian_integrable hg ha),
        delta_sub_head hf hg [a] hhs]
      ring
    | cons b bs =>
      simpa only [cumulant] using delta_sub_head hf hg (a :: b :: bs) hhs

theorem cumulant_add_head {f g : FourierProfile} (hf : IsProfile f) (hg : IsProfile g)
    (hs : List FourierProfile) (hhs : ∀ h ∈ hs, IsProfile h) :
    cumulant ((f + g) :: hs) = cumulant (f :: hs) + cumulant (g :: hs) := by
  have h := cumulant_sub_head (hf.add hg) hg hs hhs
  rw [add_sub_cancel_right] at h
  linarith

theorem convolve_const_mul_head (f g : FourierProfile) (c : ℝ) :
    convolve (fun u => c * f u) g = fun u => c * convolve f g u := by
  funext u
  simp only [convolve_apply, mul_assoc, integral_const_mul]

theorem convolve_const_mul_right (f g : FourierProfile) (c : ℝ) :
    convolve f (fun u => c * g u) = fun u => c * convolve f g u := by
  rw [convolve_comm f, convolve_const_mul_head, convolve_comm g f]


private theorem oddProfile_const_mul (f : FourierProfile) (c : ℝ) :
    oddProfile (fun u => c * f u) = fun u => c * oddProfile f u := by
  funext u
  unfold oddProfile
  split_ifs <;> ring

private theorem delta_const_mul_head (f : FourierProfile) (hs : List FourierProfile) (c : ℝ) :
    delta ((fun u => c * f u) :: hs) = c * delta (f :: hs) := by
  have hlin : convolutionList (((fun u => c * f u) :: hs).map oddProfile) =
      fun u => c * convolutionList ((f :: hs).map oddProfile) u := by
    simp only [List.map_cons, oddProfile_const_mul]
    cases hs <;> simp only [List.map, convolutionList, convolve_const_mul_head]
  simp only [delta, List.length_cons, hlin, integral_const_mul]
  ring

theorem cumulant_const_mul_head (f : FourierProfile) (hs : List FourierProfile) (c : ℝ) :
    cumulant ((fun u => c * f u) :: hs) = c * cumulant (f :: hs) := by
  cases hs with
  | nil =>
    simp only [cumulant, intervalIntegral.integral_const_mul]
    ring
  | cons a rest =>
    cases rest with
    | nil =>
      have hr : (fun u : ℝ => |u| * (c * f u) * a u) = fun u => c * (|u| * f u * a u) := by
        funext u
        ring
      simp only [cumulant, hr, integral_const_mul, delta_const_mul_head]
      ring
    | cons b bs =>
      exact delta_const_mul_head f (a :: b :: bs) c


theorem IsProfile.of_even_continuous_truncate (s : ℝ) {f : FourierProfile}
    (he : Function.Even f) (hc : Continuous f) :
    IsProfile ((Set.Icc (-s) s).indicator f) := by
  let I := Set.Icc (-s) s
  have hI : IsCompact I := isCompact_Icc
  have hneg (u : ℝ) : -u ∈ I ↔ u ∈ I := by
    change -u ∈ Set.Icc (-s) s ↔ u ∈ Set.Icc (-s) s
    simp only [Set.mem_Icc]
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  refine ⟨hc.measurable.indicator hI.measurableSet, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ I
    · rw [Set.indicator_of_mem ((hneg u).2 hu), Set.indicator_of_mem hu, he u]
    · rw [Set.indicator_of_notMem (mt (hneg u).1 hu), Set.indicator_of_notMem hu]
  · refine ((hI.image hc).isBounded.union (Bornology.isBounded_singleton (x := (0 : ℝ)))).subset ?_
    rintro _ ⟨u, rfl⟩
    by_cases hu : u ∈ I
    · rw [Set.indicator_of_mem hu]
      exact Or.inl ⟨u, hu, rfl⟩
    · rw [Set.indicator_of_notMem hu]
      exact Or.inr rfl
  · apply HasCompactSupport.of_support_subset_isCompact hI
    intro u hu
    by_contra h
    exact hu (Set.indicator_of_notMem h _)

theorem Hstar_isProfile : IsProfile Hstar := by
  unfold Hstar
  apply IsProfile.of_even_continuous_truncate
  · intro u
    simp only [abs_neg]
  · unfold trigTaylor trigTerm
    fun_prop

theorem rectangle_isProfile (a : ℝ) : IsProfile (rectangle a) := by
  exact IsProfile.of_even_continuous_truncate a (Function.Even.const 1) continuous_const

theorem profileL1_rectangle {a : ℝ} (ha : 0 ≤ a) : profileL1 (rectangle a) = 2 * a := by
  have heq : (fun u => |rectangle a u|) = (Set.Icc (-a) a).indicator (fun _ => 1) := by
    funext u
    by_cases hu : u ∈ Set.Icc (-a) a <;> simp [rectangle, hu]
  rw [profileL1, heq, integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
  rw [max_eq_left (by linarith)]
  simp
  ring

/-- Error enclosure for central products with at least two rectangle factors. -/
theorem central_error_higher {η : FourierProfile} (hH : IsProfile H)
    (hη : IsProfile η) (A : List ℝ) (hlen : 2 ≤ A.length) (hA : ∀ a ∈ A, 0 ≤ a) :
    |cumulant (convolve H η :: A.map rectangle) -
        cumulant (convolve Hstar η :: A.map rectangle)| ≤
      (2 : ℝ)^A.length * (2 / (10 : ℝ)^12 * profileL1 η) *
        (A.map fun a => 2 * a).prod := by
  let e := convolve (H - Hstar) η
  have he : IsProfile e := convolve_isProfile (hH.sub Hstar_isProfile) hη
  have hs : ∀ p ∈ A.map rectangle, IsProfile p := by
    intro p hp
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    exact rectangle_isProfile a
  rw [← cumulant_sub_head (convolve_isProfile hH hη) (convolve_isProfile Hstar_isProfile hη) _ hs,
    ← convolve_sub_head hH Hstar_isProfile (integrable_of_isProfile hη)]
  have hlong : cumulant (e :: A.map rectangle) = delta (e :: A.map rectangle) := by
    cases A with
    | nil => simp at hlen
    | cons a rest =>
      cases rest with
      | nil => simp at hlen
      | cons b bs => rfl
  change |cumulant (e :: A.map rectangle)| ≤ _
  rw [hlong]
  have hδ := abs_delta_le (e :: A.map rectangle) (fun g hg => by
    rcases List.mem_cons.mp hg with rfl | ht
    · exact he
    · exact hs g ht)
  simp only [List.length_cons, List.length_map, Nat.add_sub_cancel, List.map_cons, List.prod_cons,
    List.map_map] at hδ
  have hrhs : (A.map (profileL1 ∘ rectangle)).prod = (A.map fun a => 2 * a).prod := by
    congr 1
    exact List.map_congr_left fun a ha => profileL1_rectangle (hA a ha)
  rw [hrhs] at hδ
  have herr := (profileL1_convolve_le (integrable_of_isProfile (hH.sub Hstar_isProfile))
    (integrable_of_isProfile hη)).trans
      (mul_le_mul_of_nonneg_right Hstar_integral_error (profileL1_nonneg η))
  have hprod : 0 ≤ (A.map fun a => 2 * a).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact mul_nonneg (by norm_num) (hA t ht)
  exact hδ.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right herr hprod) (by positivity)
    |>.trans_eq (by ring))


private theorem abs_weighted_intervalIntegral_le {a b C : ℝ} (hab : a ≤ b)
    {w e : ℝ → ℝ} (hw : Continuous w) (hwn : ∀ u ∈ Set.Ioc a b, 0 ≤ w u)
    (he : ∀ u, |e u| ≤ C) :
    |∫ u in a..b, w u * e u| ≤ (∫ u in a..b, w u) * C := by
  rw [← intervalIntegral.integral_mul_const, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  have hnorm : |∫ u in Set.Ioc a b, w u * e u| ≤ ∫ u in Set.Ioc a b, |w u * e u| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a b))
        (f := fun u => w u * e u))
  refine hnorm.trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    ((hw.intervalIntegrable a b).1.mul_const C) ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [abs_mul, abs_of_nonneg (hwn u hu)]
  exact mul_le_mul_of_nonneg_left (he u) (hwn u hu)

private theorem triangle_integral (a : ℝ) (ha : 0 ≤ a) :
    (∫ u in (1 - a)..(1 + a), a - |1 - u|) = a^2 := by
  have hL : 1 - a ≤ 1 := by linarith
  have hR : 1 ≤ 1 + a := by linarith
  let w := fun u : ℝ => a - |1 - u|
  have hw : Continuous w := by dsimp [w]; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (hw.intervalIntegrable _ _) (hw.intervalIntegrable _ _)]
  have hl : (∫ u in (1 - a)..1, w u) = ∫ u in (1 - a)..1, u + (a - 1) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hL]
    intro u hu
    dsimp [w]
    rw [abs_of_nonneg (by linarith [hu.2] : 0 ≤ 1 - u)]
    ring
  have hr : (∫ u in 1..(1 + a), w u) = ∫ u in 1..(1 + a), (a + 1) - u := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hR]
    intro u hu
    dsimp [w]
    rw [abs_of_nonpos (by linarith [hu.1] : 1 - u ≤ 0)]
    ring
  change (∫ u in (1 - a)..1, w u) + (∫ u in 1..(1 + a), w u) = _
  rw [hl, hr]
  have hleft := intervalIntegral.integral_add (μ := volume)
    (f := fun u : ℝ => u) (g := fun _ => a - 1)
    (continuous_id.intervalIntegrable (1-a) 1) (continuous_const.intervalIntegrable _ _)
  have hright := intervalIntegral.integral_sub (μ := volume)
    (f := fun _ => a + 1) (g := fun u : ℝ => u)
    (continuous_const.intervalIntegrable 1 (1+a)) (continuous_id.intervalIntegrable _ _)
  rw [hleft, hright, integral_id, integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The uniform bound in the covariance case of the central error. -/
theorem abs_covariance_le_of_formula {e : FourierProfile} {a C : ℝ} (ha : 0 ≤ a)
    (he : ∀ u, |e u| ≤ C)
    (hf : cumulant [e, rectangle a] =
      (4 * ∫ u in (0 : ℝ)..a, u * e u) -
        (2 * ∫ u in (1 - a)..(1 + a), (a - |1 - u|) * e u)) :
    |cumulant [e, rectangle a]| ≤ 4 * a^2 * C := by
  have h1 := abs_weighted_intervalIntegral_le ha (w := id) continuous_id
    (fun _ hu => hu.1.le) he
  rw [show (∫ u in (0 : ℝ)..a, id u) = a^2 / 2 by simp [integral_id]] at h1
  have h2 := abs_weighted_intervalIntegral_le (by linarith : 1 - a ≤ 1 + a)
    (w := fun u => a - |1 - u|) (by fun_prop)
    (fun u hu => sub_nonneg.mpr (abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩)) he
  rw [triangle_integral a ha] at h2
  rw [hf]
  refine (abs_sub _ _).trans ?_
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 4 * (a^2 / 2 * C) + 2 * (a^2 * C) := by
      exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
        (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring


/-- The covariance case of the central error, using the evaluation in Lemma 27. -/
theorem central_error_single {η : FourierProfile} (hη : IsProfile η)
    {a : ℝ} (ha : a ∈ Set.Ioc (0 : ℝ) 1) :
    |cumulant [convolve H η, rectangle a] - cumulant [convolve Hstar η, rectangle a]| ≤
      4 * a^2 * profileL1 η / (10 : ℝ)^12 := by
  have hH := H_isProfile
  let e := convolve (H - Hstar) η
  have he : IsProfile e := convolve_isProfile (hH.sub Hstar_isProfile) hη
  have hem : ∀ u, |e u| ≤ profileL1 η * (1 / (10 : ℝ)^12) := by
    intro u
    dsimp only [e]
    rw [convolve_comm (H - Hstar)]
    exact abs_convolve_le_of_right_bound (integrable_of_isProfile hη) Hstar_pointwise_error u
  rw [← cumulant_sub_head (convolve_isProfile hH hη) (convolve_isProfile Hstar_isProfile hη)
    [rectangle a] (by simp [rectangle_isProfile]),
    ← convolve_sub_head hH Hstar_isProfile (integrable_of_isProfile hη)]
  exact (abs_covariance_le_of_formula ha.1.le hem (cumulant_covariance e he a ha)).trans_eq (by ring)

end Chowla
