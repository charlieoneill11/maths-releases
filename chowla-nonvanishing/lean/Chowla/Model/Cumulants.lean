import Chowla.Certificate
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace Chowla

open Filter MeasureTheory Set
open scoped BigOperators Convolution Pointwise Topology

abbrev FourierProfile := ℝ → ℝ

noncomputable def profileL1 (h : FourierProfile) : ℝ := ∫ u : ℝ, |h u|

theorem integrable_of_isProfile {h : FourierProfile} (hh : IsProfile h) : Integrable h := by
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.mp hh.2.2.1)
  have hg : IntegrableOn h (tsupport h) :=
    Measure.integrableOn_of_bounded hh.2.2.2.isCompact.measure_ne_top
      hh.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hC (h x) ⟨x, rfl⟩)
  exact (integrableOn_iff_integrable_of_support_subset subset_closure).mp hg

theorem convolve_apply (h g : FourierProfile) (u : ℝ) :
    convolve h g u = ∫ t : ℝ, h t * g (u - t) := rfl

theorem convolve_comm (h g : FourierProfile) : convolve h g = convolve g h := by
  funext u
  rw [convolve_apply, convolve_apply, ← integral_sub_left_eq_self (fun t => g t * h (u - t)) volume u]
  simp_rw [sub_sub_cancel, mul_comm]

theorem convolve_congr {h h' g g' : FourierProfile} (hh : h =ᵐ[volume] h')
    (hg : g =ᵐ[volume] g') : convolve h g = convolve h' g' :=
  convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) hh hg

theorem integrable_convolve {h g : FourierProfile} (hh : Integrable h) (hg : Integrable g) :
    Integrable (convolve h g) :=
  hh.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg

theorem integral_convolve {h g : FourierProfile} (hh : Integrable h) (hg : Integrable g) :
    (∫ t : ℝ, convolve h g t) = (∫ t : ℝ, h t) * (∫ t : ℝ, g t) := by
  simpa only [convolve, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    (integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hh hg)

theorem convolve_hasRadiusAtMost {h g : FourierProfile} {b c : ℝ}
    (hh : HasRadiusAtMost h b) (hg : HasRadiusAtMost g c) :
    HasRadiusAtMost (convolve h g) (b + c) := by
  classical
  refine ⟨add_nonneg hh.1 hg.1, ?_⟩
  let h' := (Icc (-b) b).indicator h
  let g' := (Icc (-c) c).indicator g
  have h_eq : h =ᵐ[volume] h' := by
    filter_upwards [hh.2] with u hu
    by_cases hm : u ∈ Icc (-b) b
    · simp [h', hm]
    · simpa [h', hm] using hu hm
  have g_eq : g =ᵐ[volume] g' := by
    filter_upwards [hg.2] with u hu
    by_cases hm : u ∈ Icc (-c) c
    · simp [g', hm]
    · simpa [g', hm] using hu hm
  rw [convolve_congr h_eq g_eq]
  filter_upwards with u hu
  rw [convolve_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases ht : t ∈ Icc (-b) b
  · by_cases hut : u - t ∈ Icc (-c) c
    · exact (hu ⟨by linarith [ht.1, hut.1], by linarith [ht.2, hut.2]⟩).elim
    · simp [g', hut]
  · simp [h', ht]

theorem HasRadiusAtMost.oddProfile {h : FourierProfile} {b : ℝ}
    (hh : HasRadiusAtMost h b) : HasRadiusAtMost (oddProfile h) b := by
  refine ⟨hh.1, ?_⟩
  filter_upwards [hh.2] with u hu h
  simp [Chowla.oddProfile, hu h]

theorem measurable_oddProfile {h : FourierProfile} (hh : Measurable h) :
    Measurable (oddProfile h) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) hh.neg
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) hh measurable_const)

theorem abs_oddProfile_le (h : FourierProfile) (u : ℝ) : |oddProfile h u| ≤ |h u| := by
  unfold oddProfile
  split_ifs <;> simp

theorem integrable_oddProfile {h : FourierProfile} (hm : Measurable h) (hi : Integrable h) :
    Integrable (oddProfile h) :=
  hi.mono (measurable_oddProfile hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using abs_oddProfile_le h u)

private theorem forall₂_oddProfile {hs : List FourierProfile} {b : List ℝ}
    (hb : List.Forall₂ HasRadiusAtMost hs b) :
    List.Forall₂ HasRadiusAtMost (hs.map oddProfile) b := by
  induction hb with
  | nil => exact .nil
  | cons h₁ _ ih => exact .cons h₁.oddProfile ih

theorem convolutionList_hasRadiusAtMost {hs : List FourierProfile} {b : List ℝ}
    (hb : List.Forall₂ HasRadiusAtMost hs b) :
    HasRadiusAtMost (convolutionList hs) b.sum := by
  induction hb with
  | nil => simp [HasRadiusAtMost, convolutionList]
  | @cons h r hs bs hr hrs ih =>
    cases hrs with
    | nil => simpa [convolutionList] using hr
    | cons _ _ =>
      simpa only [List.sum_cons, convolutionList] using convolve_hasRadiusAtMost hr ih

/-- Lemma 6(a). The sum of the support bounds confines the convolution to the unit interval. -/
theorem delta_eq_zero_of_support (hs : List FourierProfile) (b : List ℝ)
    (_hhs : ∀ h ∈ hs, IsProfile h)
    (hb : List.Forall₂ HasRadiusAtMost hs b) (hsmall : b.sum ≤ 1) :
    delta hs = 0 := by
  have hb' := forall₂_oddProfile hb
  have hzero : (∫ u in Ioi (1 : ℝ), convolutionList (hs.map oddProfile) u) = 0 := by
    apply integral_eq_zero_of_ae
    have he := (convolutionList_hasRadiusAtMost hb').2
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioi] with u hz hu
    exact hz fun hm => (not_lt_of_ge (hm.2.trans hsmall)) hu
  simp [delta, hzero]

/-- Lemma 6(c). Disjoint blocks of total width at most two cannot both contribute tails. -/
theorem delta_mul_delta_eq_zero (hs gs : List FourierProfile)
    (b c : List ℝ) (hhs : ∀ h ∈ hs ++ gs, IsProfile h)
    (hb : List.Forall₂ HasRadiusAtMost hs b) (hc : List.Forall₂ HasRadiusAtMost gs c)
    (hsmall : b.sum + c.sum ≤ 2) :
    delta hs * delta gs = 0 := by
  by_cases h : b.sum ≤ 1
  · rw [delta_eq_zero_of_support hs b (fun g hg => hhs g (List.mem_append_left _ hg)) hb h,
      zero_mul]
  · have hc' : c.sum ≤ 1 := by linarith
    rw [delta_eq_zero_of_support gs c (fun g hg => hhs g (List.mem_append_right _ hg)) hc hc',
      mul_zero]

theorem profileL1_nonneg (h : FourierProfile) : 0 ≤ profileL1 h :=
  integral_nonneg fun _ => abs_nonneg _

theorem abs_convolve_le (h g : FourierProfile) (u : ℝ) :
    |convolve h g u| ≤ convolve (fun t => |h t|) (fun t => |g t|) u := by
  rw [convolve_apply, convolve_apply, ← Real.norm_eq_abs]
  simpa only [Real.norm_eq_abs, abs_mul] using
    (norm_integral_le_integral_norm (f := fun t : ℝ => h t * g (u - t)))

theorem profileL1_convolve_le {h g : FourierProfile} (hh : Integrable h) (hg : Integrable g) :
    profileL1 (convolve h g) ≤ profileL1 h * profileL1 g := by
  rw [profileL1, profileL1, profileL1, ← integral_convolve hh.abs hg.abs]
  exact integral_mono (integrable_convolve hh hg).abs
    (integrable_convolve hh.abs hg.abs) (abs_convolve_le h g)

theorem convolutionList_integrable {hs : List FourierProfile}
    (hhs : ∀ h ∈ hs, Integrable h) : Integrable (convolutionList hs) := by
  induction hs with
  | nil => exact integrable_zero _ _ _
  | cons h hs ih =>
    have hh := hhs h (by simp)
    cases hs with
    | nil => exact hh
    | cons g gs =>
      exact integrable_convolve hh (ih fun t ht => hhs t (List.mem_cons_of_mem h ht))

theorem profileL1_convolutionList_le {hs : List FourierProfile}
    (hhs : ∀ h ∈ hs, Integrable h) :
    profileL1 (convolutionList hs) ≤ (hs.map profileL1).prod := by
  induction hs with
  | nil => simp [convolutionList, profileL1]
  | cons h hs ih =>
    cases hs with
    | nil => simp [convolutionList]
    | cons g gs =>
      have hh := hhs h (by simp)
      have htail : ∀ t ∈ g :: gs, Integrable t :=
        fun t ht => hhs t (List.mem_cons_of_mem h ht)
      change profileL1 (convolve h (convolutionList (g :: gs))) ≤
        profileL1 h * ((g :: gs).map profileL1).prod
      exact (profileL1_convolve_le hh (convolutionList_integrable htail)).trans
        (mul_le_mul_of_nonneg_left (ih htail) (profileL1_nonneg h))

theorem profileL1_oddProfile_le {h : FourierProfile} (hm : Measurable h) (hi : Integrable h) :
    profileL1 (oddProfile h) ≤ profileL1 h :=
  integral_mono (integrable_oddProfile hm hi).abs hi.abs (abs_oddProfile_le h)

/-- Lemma 6(b). Young's inequality for the convolution in the restricted tail. -/
theorem abs_delta_le (hs : List FourierProfile) (hhs : ∀ h ∈ hs, IsProfile h) :
    |delta hs| ≤ (2 : ℝ) ^ (hs.length - 1) * (hs.map profileL1).prod := by
  cases hs with
  | nil => simp [delta, convolutionList]
  | cons h hs =>
    have hh : ∀ g ∈ h :: hs, Integrable g := fun g hg => integrable_of_isProfile (hhs g hg)
    have hodd : ∀ g ∈ (h :: hs).map oddProfile, Integrable g := by
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
      exact integrable_oddProfile (hhs j hj).1 (hh j hj)
    have hi := convolutionList_integrable hodd
    have hI : |∫ u in Ioi (1 : ℝ), convolutionList ((h :: hs).map oddProfile) u| ≤
        profileL1 (convolutionList ((h :: hs).map oddProfile)) := by
      refine le_trans ?_ (setIntegral_le_integral (s := Ioi (1 : ℝ)) (hi.abs) (Filter.Eventually.of_forall fun _ => abs_nonneg _))
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := volume.restrict (Ioi (1 : ℝ))) (f := convolutionList ((h :: hs).map oddProfile)))
    have hp : (((h :: hs).map oddProfile).map profileL1).prod ≤
        ((h :: hs).map profileL1).prod := by
      rw [List.map_map]
      apply List.prod_map_le_prod_map₀
      · intro g _
        exact profileL1_nonneg _
      · intro g hg
        exact profileL1_oddProfile_le (hhs g hg).1 (hh g hg)
    have hc : |-((-2 : ℝ) ^ (h :: hs).length) / 2| = (2 : ℝ) ^ hs.length := by
      rw [abs_div, abs_neg, abs_pow, List.length_cons, pow_succ]
      norm_num
    rw [delta, abs_mul, hc]
    exact mul_le_mul_of_nonneg_left (hI.trans ((profileL1_convolutionList_le hodd).trans hp)) (by positivity)

theorem HasRadiusAtMost.mono {h : FourierProfile} {r s : ℝ}
    (hr : HasRadiusAtMost h r) (hrs : r ≤ s) : HasRadiusAtMost h s := by
  refine ⟨hr.1.trans hrs, ?_⟩
  filter_upwards [hr.2] with u hu h
  exact hu fun hm => h ⟨(neg_le_neg hrs).trans hm.1, hm.2.trans hrs⟩

theorem hasRadiusAtMost_radius {h : FourierProfile} (hh : IsProfile h) :
    HasRadiusAtMost h (radius h) := by
  let bounds := {r | HasRadiusAtMost h r}
  have hnonempty : bounds.Nonempty := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hh.2.2.2.isCompact.isBounded
    refine ⟨max 0 C, le_max_left .., ?_⟩
    filter_upwards with u hu
    by_contra hhu
    have hu' : u ∈ tsupport h := subset_closure hhu
    have hbound : |u| ≤ max 0 C := (by simpa only [Real.norm_eq_abs] using hC u hu' :
      |u| ≤ C).trans (le_max_right ..)
    exact hu (abs_le.mp hbound)
  have hb (q : ℚ) : radius h < (q : ℝ) → HasRadiusAtMost h (q : ℝ) := by
    intro hq
    obtain ⟨r, hr, hrq⟩ := exists_lt_of_csInf_lt hnonempty hq
    exact HasRadiusAtMost.mono hr hrq.le
  have hforall : ∀ᵐ u ∂volume, ∀ q : ℚ, radius h < (q : ℝ) →
      u ∉ Icc (-(q : ℝ)) (q : ℝ) → h u = 0 := by
    rw [ae_all_iff]
    intro q
    by_cases hq : radius h < (q : ℝ)
    · filter_upwards [(hb q hq).2] with u hu _
      exact hu
    · filter_upwards with u h
      exact (hq h).elim
  refine ⟨le_csInf hnonempty (fun _ hr => hr.1), ?_⟩
  filter_upwards [hforall] with u hu hout
  have habs : radius h < |u| := lt_of_not_ge fun h => hout (abs_le.mp h)
  obtain ⟨q, hq, hqu⟩ := exists_rat_btwn habs
  exact hu q hq fun hm => (not_le_of_gt hqu) (abs_le.mpr hm)

theorem radius_nonneg {h : FourierProfile} (hh : IsProfile h) : 0 ≤ radius h :=
  (hasRadiusAtMost_radius hh).1

theorem radius_le_of_hasRadiusAtMost {h : FourierProfile} {b : ℝ} (hb : HasRadiusAtMost h b) :
    radius h ≤ b :=
  csInf_le (show BddBelow {r | HasRadiusAtMost h r} from ⟨0, fun _ hr => hr.1⟩) hb

theorem abs_convolve_le_of_right_bound {h g : FourierProfile} (hh : Integrable h)
    {C : ℝ} (hC : ∀ t : ℝ, |g t| ≤ C) (u : ℝ) :
    |convolve h g u| ≤ profileL1 h * C := by
  refine (abs_convolve_le h g u).trans ?_
  rw [convolve_apply, profileL1, ← integral_mul_const]
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (Integrable.mul_const hh.abs C)
    (Filter.Eventually.of_forall fun t => mul_le_mul_of_nonneg_left (hC (u - t)) (abs_nonneg _))

theorem measurable_convolve {h g : FourierProfile} (hh : Measurable h) (hg : Measurable g) :
    Measurable (convolve h g) := by
  have hm : Measurable (fun p : ℝ × ℝ => h p.2 * g (p.1 - p.2)) :=
    (hh.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem convolve_isProfile {h g : FourierProfile} (hh : IsProfile h) (hg : IsProfile g) :
    IsProfile (convolve h g) := by
  refine ⟨measurable_convolve hh.1 hg.1, ?_, ?_,
    hh.2.2.2.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg.2.2.2⟩
  · intro u
    exact convolution_neg_of_neg_eq (ContinuousLinearMap.lsmul ℝ ℝ)
      (Filter.Eventually.of_forall hh.2.1) (Filter.Eventually.of_forall hg.2.1)
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hg.2.2.1
    refine isBounded_iff_forall_norm_le.mpr ⟨profileL1 h * C, ?_⟩
    rintro _ ⟨u, rfl⟩
    simpa only [Real.norm_eq_abs] using
      (abs_convolve_le_of_right_bound (integrable_of_isProfile hh)
        (fun t => by simpa only [Real.norm_eq_abs] using hC (g t) ⟨t, rfl⟩) u)

theorem radius_convolve_le {h g : FourierProfile} (hh : IsProfile h) (hg : IsProfile g) :
    radius (convolve h g) ≤ radius h + radius g :=
  radius_le_of_hasRadiusAtMost
    (convolve_hasRadiusAtMost (hasRadiusAtMost_radius hh) (hasRadiusAtMost_radius hg))

end Chowla
