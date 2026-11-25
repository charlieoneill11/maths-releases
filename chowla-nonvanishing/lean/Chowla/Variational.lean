import Chowla.VariationalKernel
import Chowla.VariationalModel
import Chowla.EnclosureProofs

namespace Chowla

open Filter Function MeasureTheory MvPolynomial Set
open scoped BigOperators Topology

private noncomputable def smoothingScale (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 3)
private noncomputable def smoothingRadius (r n : ℕ) : ℝ := (1 - smoothingScale n) / (2 * (r + 1))

private theorem smoothingScale_bounds (n : ℕ) : 1 / 2 < smoothingScale n ∧ smoothingScale n < 1 := by
  unfold smoothingScale
  have h₁ : (0 : ℝ) < 1 / ((n : ℝ) + 3) := by positivity
  have h₂ : 1 / ((n : ℝ) + 3) < 1 / 2 := by
    apply div_lt_div_of_pos_left one_pos (by norm_num)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  constructor <;> linarith

private theorem smoothingScale_pos (n : ℕ) : 0 < smoothingScale n :=
  (by norm_num : (0 : ℝ) < 1 / 2).trans (smoothingScale_bounds n).1

private theorem smoothingRadius_pos (r n : ℕ) : 0 < smoothingRadius r n :=
  div_pos (sub_pos.mpr (smoothingScale_bounds n).2) (by positivity)

private theorem smoothingRadius_le_one (r n : ℕ) : smoothingRadius r n ≤ 1 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (r + 1))).2
  have h := smoothingScale_pos n
  have hr : 0 ≤ (r : ℝ) := by positivity
  linarith

private theorem smoothingScale_tendsto : Tendsto smoothingScale atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 3)) atTop (𝓝 1)
  simpa only [smoothingScale, one_div, sub_zero, comp_apply] using hc.sub (tendsto_inv_atTop_zero.comp h)

private theorem smoothingRadius_tendsto (r : ℕ) : Tendsto (smoothingRadius r) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [smoothingRadius, sub_self, zero_div] using
    (hc.sub smoothingScale_tendsto).div_const (2 * ((r : ℝ) + 1))

private noncomputable def smooth (r n : ℕ) : FourierProfile → FourierProfile :=
  smoothProfile variationalKernel.profile (smoothingScale n) (smoothingRadius r n)

private theorem smooth_isProfile (r n : ℕ) {h : FourierProfile} (hh : IsProfile h) :
    IsProfile (smooth r n h) :=
  smoothProfile_isProfile _ h variationalKernel.isProfile hh (smoothingScale_pos n) (smoothingRadius_pos r n)

private theorem smooth_props (r n : ℕ) {h : FourierProfile} (hh : IsProfile h) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smooth r n h) ∧
      (∫ u : ℝ, smooth r n h u) = (∫ u : ℝ, h u) ∧
      HasRadiusAtMost (smooth r n h) (smoothingScale n * radius h + smoothingRadius r n) :=
  smoothProfile_properties _ h _ _ variationalKernel.isProfile variationalKernel.smooth
    variationalKernel_radius variationalKernel_mass hh (smoothingScale_pos n) (smoothingRadius_pos r n)

private noncomputable def smoothTest (r n : ℕ) (h : FourierProfile) (hh : IsProfile h) : SmoothProfile :=
  ⟨smooth r n h, smooth_isProfile r n hh, (smooth_props r n hh).1⟩

private theorem smooth_radius (r n : ℕ) {h : FourierProfile} (hh : IsProfile h) :
    radius (smooth r n h) ≤ smoothingScale n * radius h + smoothingRadius r n :=
  radius_le_of_hasRadiusAtMost (smooth_props r n hh).2.2

private theorem smooth_profileConverges (r : ℕ) {h : FourierProfile} (hh : IsProfile h) :
    ProfileConverges (fun n => smooth r n h) h := by
  refine ⟨hh, fun n => smooth_isProfile r n hh, ?_, ?_⟩
  · obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hh.2.2.1
    have hB' (u : ℝ) : |h u| ≤ B := hB _ ⟨u, rfl⟩
    have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
    have hr := hasRadiusAtMost_radius hh
    refine ⟨2 * B, radius h + 1, by positivity, hr.mono (by linarith), ?_, ?_⟩
    · intro n u
      have hinv := (inv_le_iff_one_le_mul₀ (smoothingScale_pos n)).2
        (show 1 ≤ 2 * smoothingScale n by linarith [(smoothingScale_bounds n).1])
      exact (smoothProfile_sup _ h variationalKernel.isProfile variationalKernel_nonnegative
        variationalKernel_mass (smoothingScale_pos n) (smoothingRadius_pos r n) hB' u).trans
        (mul_le_mul_of_nonneg_right hinv hB₀)
    · intro n
      exact (smooth_props r n hh).2.2.mono (add_le_add
        (mul_le_of_le_one_left hr.1 (smoothingScale_bounds n).2.le) (smoothingRadius_le_one r n))
  · exact smoothProfile_L1_tendsto _ h variationalKernel.isProfile variationalKernel_nonnegative
      variationalKernel_mass variationalKernel_support (integrable_of_isProfile hh) smoothingScale_pos
      (smoothingRadius_pos r) smoothingScale_tendsto (smoothingRadius_tendsto r)

private theorem smoothing_rectangles_bandwidth (r n : ℕ) (A : List ℝ) (hA : ∀ a ∈ A, 0 ≤ a) :
    MomentWord.bandwidth (A.map fun a => (smoothTest r n (rectangle a) (rectangle_isProfile a)).test) ≤
      smoothingScale n * A.sum + (A.length : ℝ) * smoothingRadius r n := by
  induction A with
  | nil => simp [MomentWord.bandwidth]
  | cons a A ih =>
      have ha := smooth_radius r n (rectangle_isProfile a)
      have har := radius_le_of_hasRadiusAtMost (rectangle_hasRadiusAtMost (hA _ (List.mem_cons_self ..)))
      have hs := mul_le_mul_of_nonneg_left har (smoothingScale_pos n).le
      have ht := ih (fun b hb => hA b (List.mem_cons_of_mem _ hb))
      simp only [MomentWord.bandwidth, List.map_cons, List.sum_cons, SmoothProfile.test_profile]
      change radius (smooth r n (rectangle a)) + MomentWord.bandwidth
        (A.map fun a => (smoothTest r n (rectangle a) (rectangle_isProfile a)).test) ≤ _
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, add_mul]
      linarith only [ha, hs, ht]

private theorem wickStatistic_nil (X : ℝ) (d : ℤ) : wickStatistic [] X d = 1 := by
  classical
  let U : Finset (Fin 0) := Finset.univ
  have hu : U = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ => Fin.elim0 i)
  have hp (P : Finpartition U) : P.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr hu
  have hparts : (Finset.univ : Finset (Finpartition U)) = {⊥} := by
    ext P
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Finpartition.ext ((hp P).trans (hp ⊥).symm)
  rw [wickStatistic, ← MomentPolynomial.eval_real]
  unfold wickPolynomial
  change MomentPolynomial.eval _ _ (MomentPolynomial.sum
    (((Finset.univ : Finset (Finpartition U)).filter _).toList.map _)) = _
  rw [hparts]
  rw [Finset.filter_eq_self.mpr (fun P _ B hB => (Finset.notMem_empty B (hp P ▸ hB)).elim)]
  simp [MomentPolynomial.eval_sum, MomentPolynomial.eval_prod, hp]

private noncomputable def augmentedRow (F : Amplitude) : Fin (F.length + 1) → Row :=
  Fin.cases ⟨[], H⟩ F.get

private noncomputable def augmentedCoefficient {F : Amplitude} (z : ℝ) : Fin (F.length + 1) → ℝ :=
  Fin.cases 1 (fun _ => -z)

private theorem augmentedRow_isProfile {F : Amplitude} (hF : IsAmplitude F) (i : Fin (F.length + 1)) :
    IsProfile (augmentedRow F i).profile :=
  Fin.cases H_isProfile (fun j => (hF _ (List.get_mem _ j)).2.1) i

private theorem augmentedRow_budget {F : Amplitude} (hF : IsAmplitude F) (i : Fin (F.length + 1)) :
    radius (augmentedRow F i).profile + (augmentedRow F i).widths.sum ≤ 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [augmentedRow] using radius_le_of_hasRadiusAtMost H_hasRadiusAtMost
  · have hj := (hF _ (List.get_mem _ j)).2.2.2
    simpa [augmentedRow] using (le_sub_iff_add_le.mp hj)

private theorem augmentedRow_width_nonnegative {F : Amplitude} (hF : IsAmplitude F)
    (i : Fin (F.length + 1)) : ∀ a ∈ (augmentedRow F i).widths, 0 ≤ a := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [augmentedRow]
  · intro a ha
    exact ((hF _ (List.get_mem _ j)).1 a ha).1.le

private noncomputable def smoothedAmplitudeProfile {F : Amplitude} (hF : IsAmplitude F) (r n : ℕ)
    (i : Fin (F.length + 1)) : SmoothProfile :=
  smoothTest r n (augmentedRow F i).profile (augmentedRow_isProfile hF i)

private noncomputable def smoothedAmplitudeRectangles (F : Amplitude) (r n : ℕ)
    (i : Fin (F.length + 1)) : List MomentTest :=
  (augmentedRow F i).widths.map fun a => (smoothTest r n (rectangle a) (rectangle_isProfile a)).test

private theorem smoothedAmplitudeRectangles_profiles (F : Amplitude) (r n : ℕ) (i : Fin (F.length + 1)) :
    (smoothedAmplitudeRectangles F r n i).map MomentTest.profile =
      (((augmentedRow F i).widths).map rectangle).map (smooth r n) := by
  simp [smoothedAmplitudeRectangles, smoothTest, List.map_map, Function.comp_def]

private theorem smoothedAmplitude_bandwidth {F : Amplitude} (hF : IsAmplitude F) (r n : ℕ)
    (hr : ∀ i : Fin (F.length + 1), (augmentedRow F i).widths.length ≤ r)
    (i : Fin (F.length + 1)) :
    radius (smoothedAmplitudeProfile hF r n i).profile +
      MomentWord.bandwidth (smoothedAmplitudeRectangles F r n i) < 1 := by
  have h₁ := smooth_radius r n (augmentedRow_isProfile hF i)
  have h₂ := smoothing_rectangles_bandwidth r n _ (augmentedRow_width_nonnegative hF i)
  have hc : ((augmentedRow F i).widths.length : ℝ) ≤ r := by exact_mod_cast hr i
  have hb := augmentedRow_budget hF i
  have hs := smoothingScale_pos n
  have hd := smoothingRadius_pos r n
  have he : (r + 1 : ℝ) * smoothingRadius r n = (1 - smoothingScale n) / 2 := by
    unfold smoothingRadius
    have h : (r + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  have hle := add_le_add h₁ h₂
  have hb' := mul_le_mul_of_nonneg_left hb hs.le
  have hc' := mul_le_mul_of_nonneg_right hc hd.le
  have hs' := (smoothingScale_bounds n).2
  change radius (smooth r n (augmentedRow F i).profile) +
    MomentWord.bandwidth (smoothedAmplitudeRectangles F r n i) < 1
  change radius (smooth r n (augmentedRow F i).profile) +
    MomentWord.bandwidth (smoothedAmplitudeRectangles F r n i) ≤ _ at hle
  nlinarith only [hle, hb', hc', he, hs']

private theorem smoothedAmplitude_zero {F : Amplitude} (hF : IsAmplitude F) (z : ℝ) (r n : ℕ)
    (X : ℝ) (d : ℤ) :
    ∑ i : Fin (F.length + 1), augmentedCoefficient z i *
      wickStatistic (smoothedAmplitudeRectangles F r n i) X d *
      (∫ u : ℝ, (smoothedAmplitudeProfile hF r n i).profile u) = 1 := by
  rw [Fin.sum_univ_succ]
  have h0 : (∫ u : ℝ, (smoothedAmplitudeProfile hF r n 0).profile u) = 1 :=
    (smooth_props r n H_isProfile).2.1.trans integral_H
  have hs (i : Fin F.length) : (∫ u : ℝ, (smoothedAmplitudeProfile hF r n i.succ).profile u) = 0 :=
    (smooth_props r n (hF _ (List.get_mem _ i)).2.1).2.1.trans (hF _ (List.get_mem _ i)).2.2.1
  simp only [hs, mul_zero, Finset.sum_const_zero, add_zero, h0, mul_one]
  change (1 : ℝ) * wickStatistic [] X d = 1
  rw [wickStatistic_nil, mul_one]

private noncomputable def amplitudeTerm (F : Amplitude) (z : ℝ)
    (i j : Fin (F.length + 1)) : ℝ :=
  augmentedCoefficient z i * augmentedCoefficient z j * modelExpectation
    (stat (convolve (augmentedRow F i).profile (augmentedRow F j).profile) *
      wickRow (augmentedRow F i) * wickRow (augmentedRow F j))

private theorem amplitudeTerm_sum (F : Amplitude) (z : ℝ) :
    ∑ i, ∑ j, amplitudeTerm F z i j = innerGG - 2 * z * inner_G F + z^2 * inner F F := by
  have h₀ : amplitudeTerm F z 0 0 = innerGG := by
    simp [amplitudeTerm, augmentedCoefficient, augmentedRow, wickRow, innerGG,
      modelExpectation_singleton _ (convolve_isProfile H_isProfile H_isProfile)]
  have h₁ (j : Fin F.length) : amplitudeTerm F z 0 j.succ = -z * innerGRow (F.get j) := by
    simp [amplitudeTerm, augmentedCoefficient, augmentedRow, wickRow, innerGRow]
  have h₂ (i : Fin F.length) : amplitudeTerm F z i.succ 0 = -z * innerGRow (F.get i) := by
    simp only [amplitudeTerm, augmentedCoefficient, augmentedRow, Fin.cases_succ, Fin.cases_zero,
      wickRow, innerGRow, List.map_nil, wick_nil, mul_one, convolve_comm (F.get i).profile H]
  have h₃ (i j : Fin F.length) : amplitudeTerm F z i.succ j.succ = z^2 * innerRow (F.get i) (F.get j) := by
    simp [amplitudeTerm, augmentedCoefficient, augmentedRow, innerRow, pow_two]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := amplitudeTerm F z 0)]
  simp only [Fin.sum_univ_succ (f := amplitudeTerm F z (Fin.succ _)), h₀, h₁, h₂, h₃,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum (f : Row → ℝ) : ∑ i : Fin F.length, f (F.get i) = (F.map f).sum := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map F f)
  simp only [inner_G, inner, ← hsum]
  ring

private theorem smoothedAmplitude_model_tendsto {F : Amplitude} (hF : IsAmplitude F) (z : ℝ) (r : ℕ) :
    Tendsto (fun n => modelExpectation (squarePolynomial Finset.univ (augmentedCoefficient z)
      (smoothedAmplitudeProfile hF r n) (smoothedAmplitudeRectangles F r n)).model)
      atTop (𝓝 (innerGG - 2 * z * inner_G F + z^2 * inner F F)) := by
  rw [← amplitudeTerm_sum F]
  have hsum (n : ℕ) : modelExpectation (squarePolynomial Finset.univ (augmentedCoefficient z)
      (smoothedAmplitudeProfile hF r n) (smoothedAmplitudeRectangles F r n)).model =
      ∑ i : Fin (F.length + 1), ∑ j : Fin (F.length + 1),
        augmentedCoefficient z i * augmentedCoefficient z j * modelExpectation
          (stat (convolve (smooth r n (augmentedRow F i).profile) (smooth r n (augmentedRow F j).profile)) *
          wick (((augmentedRow F i).widths.map rectangle).map (smooth r n)) *
          wick (((augmentedRow F j).widths.map rectangle).map (smooth r n))) := by
    rw [squarePolynomial_model]
    rw [modelExpectation_eq_linear, map_sum]
    simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [← modelExpectation_eq_linear]
    simp only [smoothedAmplitudeRectangles_profiles, smoothedAmplitudeProfile, smoothTest]
    rw [mul_assoc, mul_assoc, ← mul_assoc (stat _) _, modelExpectation_C_mul]
    exact mul_assoc _ _ _
  simp only [hsum]
  apply tendsto_finset_sum
  intro i _
  apply tendsto_finset_sum
  intro j _
  have hi := smooth_profileConverges r (augmentedRow_isProfile hF i)
  have hj := smooth_profileConverges r (augmentedRow_isProfile hF j)
  have ht := wick_model_tendsto ((augmentedRow F i).widths.map rectangle)
    ((augmentedRow F j).widths.map rectangle) _ (smooth r) _ (profileConverges_convolve hi hj)
    (profileConverges_convolve_tendsto_at hi hj 0) (by
      intro f hf
      have hf' : f ∈ ((augmentedRow F i).widths ++ (augmentedRow F j).widths).map rectangle := by
        rwa [List.map_append]
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf'
      exact smooth_profileConverges r (rectangle_isProfile a))
  exact ht.const_mul (augmentedCoefficient z i * augmentedCoefficient z j)

/-- Theorem 22 for the empty pattern. All uses of the correlations occur through `PaperClaims`. -/
theorem variational (_hGRH : DirichletLZerosOnLine) (c : CitedFacts) (m : PaperClaims)
    (D : DiscClass) (W : ShellWeight) (F : Amplitude) (hF : IsAmplitude F) (z : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X in atTop,
      (19 - Real.cot (1 / 4)) / 16 + z * inner_G F - z^2 * inner F F / 2 - ε ≤
        weightedAverage D W X nonvanishingIndicator := by
  let r := ∑ i : Fin (F.length + 1), (augmentedRow F i).widths.length
  have hr (i : Fin (F.length + 1)) : (augmentedRow F i).widths.length ≤ r :=
    Finset.single_le_sum (f := fun j => (augmentedRow F j).widths.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let Q := innerGG - 2 * z * inner_G F + z^2 * inner F F
  have hn := (smoothedAmplitude_model_tendsto hF z r).eventually
    (Iio_mem_nhds (show Q < Q + ε from lt_add_of_pos_right _ hε))
  obtain ⟨n, hn⟩ := hn.exists
  have hb (i j : Fin (F.length + 1)) :
      radius (smoothedAmplitudeProfile hF r n i).profile + radius (smoothedAmplitudeProfile hF r n j).profile +
        (MomentWord.bandwidth (smoothedAmplitudeRectangles F r n i) +
          MomentWord.bandwidth (smoothedAmplitudeRectangles F r n j)) < 2 := by
    linarith only [smoothedAmplitude_bandwidth hF r n hr i, smoothedAmplitude_bandwidth hF r n hr j]
  have hbound := weighted_nonvanishing_of_square Finset.univ (augmentedCoefficient z)
    (smoothedAmplitudeProfile hF r n) (smoothedAmplitudeRectangles F r n)
    c m D W (ε / 2) (half_pos hε) (eventually_weightedMass_pos_of_moments m D W)
    (fun i _ j _ => hb i j) (smoothedAmplitude_zero hF z r n)
  filter_upwards [hbound] with X hX
  dsimp only [Q] at hn
  rw [innerGG_eq_extremal_constant] at hn
  linarith only [hn, hX]

end Chowla
