import Chowla.Model.Cumulants

namespace Chowla

open Filter MeasureTheory Set
open scoped Topology

theorem profileL1_add_le {f g : FourierProfile} (hf : Integrable f) (hg : Integrable g) :
    profileL1 (f + g) ≤ profileL1 f + profileL1 g := by
  unfold profileL1
  rw [← integral_add hf.abs hg.abs]
  exact integral_mono (hf.add hg).abs (hf.abs.add hg.abs) fun x => abs_add_le (f x) (g x)

private theorem profileL1_congr {f g : FourierProfile} (h : f =ᵐ[volume] g) :
    profileL1 f = profileL1 g :=
  integral_congr_ae (h.fun_comp abs)

private theorem convolve_sub_split {f F g G : FourierProfile}
    (hf : Integrable f) (hF : Integrable F) (hg : Integrable g) (hG : Integrable G) :
    convolve F G - convolve f g =ᵐ[volume] convolve (F - f) G + convolve f (G - g) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have h₁ := (hF.sub hf).ae_convolution_exists L hG
  have h₂ := hf.ae_convolution_exists L (hG.sub hg)
  have h₃ := hF.ae_convolution_exists L hG
  have h₄ := hf.ae_convolution_exists L hg
  filter_upwards [h₁, h₂, h₃, h₄] with x hx₁ hx₂ hx₃ hx₄
  change Integrable (fun t : ℝ => (F t - f t) * G (x - t)) at hx₁
  change Integrable (fun t : ℝ => f t * (G (x - t) - g (x - t))) at hx₂
  change Integrable (fun t : ℝ => F t * G (x - t)) at hx₃
  change Integrable (fun t : ℝ => f t * g (x - t)) at hx₄
  simp only [Pi.sub_apply, Pi.add_apply, convolve_apply]
  rw [← integral_sub hx₃ hx₄, ← integral_add hx₁ hx₂]
  congr 1
  funext t
  ring

private theorem profileL1_convolve_sub_le {f F g G : FourierProfile}
    (hf : Integrable f) (hF : Integrable F) (hg : Integrable g) (hG : Integrable G) :
    profileL1 (convolve F G - convolve f g) ≤
      profileL1 (F - f) * profileL1 G + profileL1 f * profileL1 (G - g) := by
  rw [profileL1_congr (convolve_sub_split hf hF hg hG)]
  exact (profileL1_add_le (integrable_convolve (hF.sub hf) hG)
    (integrable_convolve hf (hG.sub hg))).trans <|
    add_le_add (profileL1_convolve_le (hF.sub hf) hG) (profileL1_convolve_le hf (hG.sub hg))

/-- Bilinear continuity in the integral of absolute value. -/
theorem profileL1_convolve_tendsto {f g : FourierProfile} {F G : ℕ → FourierProfile}
    (hf : Integrable f) (hg : Integrable g) (hF : ∀ n, Integrable (F n))
    (hG : ∀ n, Integrable (G n))
    (hFl : Tendsto (fun n => profileL1 (F n - f)) atTop (𝓝 0))
    (hGl : Tendsto (fun n => profileL1 (G n - g)) atTop (𝓝 0)) :
    Tendsto (fun n => profileL1 (convolve (F n) (G n) - convolve f g)) atTop (𝓝 0) := by
  have hbound (n : ℕ) : profileL1 (G n) ≤ profileL1 (G n - g) + profileL1 g := by
    simpa only [sub_add_cancel] using profileL1_add_le ((hG n).sub hg) hg
  have hlim : Tendsto (fun n => profileL1 (F n - f) * (profileL1 (G n - g) + profileL1 g) +
      profileL1 f * profileL1 (G n - g)) atTop (𝓝 0) := by
    simpa using (hFl.mul (hGl.add_const (profileL1 g))).add (hGl.const_mul (profileL1 f))
  refine squeeze_zero (fun _ => profileL1_nonneg _) (fun n => ?_) hlim
  exact (profileL1_convolve_sub_le hf (hF n) hg (hG n)).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hbound n) (profileL1_nonneg _)) le_rfl)

private theorem profileL1_convolutionList_tendsto {n : ℕ}
    (F : ℕ → Fin n → FourierProfile) (f : Fin n → FourierProfile)
    (hF : ∀ j i, Integrable (F j i)) (hf : ∀ i, Integrable (f i))
    (h : ∀ i, Tendsto (fun j => profileL1 (F j i - f i)) atTop (𝓝 0)) :
    Tendsto (fun j => profileL1
      (convolutionList (List.ofFn (F j)) - convolutionList (List.ofFn f))) atTop (𝓝 0) := by
  induction n with
  | zero => simp [convolutionList, profileL1]
  | succ n ih =>
    cases n with
    | zero => simpa [List.ofFn_succ, convolutionList] using h (0 : Fin 1)
    | succ n =>
      have hf' : Integrable (convolutionList (List.ofFn fun i : Fin n.succ => f i.succ)) :=
        convolutionList_integrable fun k hk => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
          exact hf i.succ
      have hF' (j : ℕ) : Integrable (convolutionList (List.ofFn fun i : Fin n.succ => F j i.succ)) :=
        convolutionList_integrable fun k hk => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
          exact hF j i.succ
      have htail := ih (fun j i => F j i.succ) (fun i => f i.succ)
        (fun j i => hF j i.succ) (fun i => hf i.succ) (fun i => h i.succ)
      have hmain := profileL1_convolve_tendsto (hf 0) hf' (fun j => hF j 0) hF' (h 0) htail
      simpa only [List.ofFn_succ, convolutionList] using hmain

private theorem integral_tendsto_of_profileL1 {f : FourierProfile} {F : ℕ → FourierProfile}
    (s : Set ℝ) (hf : Integrable f) (hF : ∀ j, Integrable (F j))
    (h : Tendsto (fun j => profileL1 (F j - f)) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ u in s, F j u) atTop (𝓝 (∫ u in s, f u)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h
  rw [← integral_sub (hF n).integrableOn hf.integrableOn]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [Real.norm_eq_abs]
  exact setIntegral_le_integral (s := s) ((hF n).sub hf).abs (Eventually.of_forall fun _ => abs_nonneg _)

theorem delta_continuity {n : ℕ} (F : ℕ → Fin n → FourierProfile) (f : Fin n → FourierProfile)
    (hF : ∀ j i, IsProfile (F j i)) (hf : ∀ i, IsProfile (f i))
    (h : ∀ i, Tendsto (fun j => profileL1 (F j i - f i)) atTop (𝓝 0)) :
    Tendsto (fun j => delta (List.ofFn (F j))) atTop (𝓝 (delta (List.ofFn f))) := by
  have hodd (i : Fin n) :
      Tendsto (fun j => profileL1 (oddProfile (F j i) - oddProfile (f i))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => profileL1_nonneg _) (fun j => ?_) (h i)
    have hs : oddProfile (F j i) - oddProfile (f i) = oddProfile (F j i - f i) := by
      funext u
      simp only [Pi.sub_apply, oddProfile]
      split_ifs <;> ring
    rw [hs]
    exact profileL1_oddProfile_le ((hF j i).1.sub (hf i).1)
      ((integrable_of_isProfile (hF j i)).sub (integrable_of_isProfile (hf i)))
  have hintF (j : ℕ) (i : Fin n) : Integrable (oddProfile (F j i)) :=
    integrable_oddProfile (hF j i).1 (integrable_of_isProfile (hF j i))
  have hintf (i : Fin n) : Integrable (oddProfile (f i)) :=
    integrable_oddProfile (hf i).1 (integrable_of_isProfile (hf i))
  have hconvF (j : ℕ) : Integrable (convolutionList (List.ofFn fun i => oddProfile (F j i))) :=
    convolutionList_integrable fun k hk => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
      exact hintF j i
  have hconvf : Integrable (convolutionList (List.ofFn fun i => oddProfile (f i))) :=
    convolutionList_integrable fun k hk => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
      exact hintf i
  have ha := profileL1_convolutionList_tendsto (fun j i => oddProfile (F j i))
    (fun i => oddProfile (f i)) hintF hintf hodd
  have ht := integral_tendsto_of_profileL1 (Ioi (1 : ℝ)) hconvf hconvF ha
  simpa only [delta, List.length_ofFn, List.map_ofFn, Function.comp_apply] using
    ht.const_mul (-((-2 : ℝ) ^ n) / 2)

private theorem integrable_weighted_product {f g : FourierProfile}
    (hf : IsProfile f) (hg : Measurable g) {R C : ℝ} (hR : HasRadiusAtMost f R)
    (hC₀ : 0 ≤ C) (hC : ∀ x : ℝ, |g x| ≤ C) :
    Integrable (fun u : ℝ => |u| * f u * g u) := by
  have h := (integrable_of_isProfile hf).abs.const_mul (R * C)
  have hm : Measurable (fun u : ℝ => |u| * f u * g u) := by
    have habs : Measurable (fun u : ℝ => |u|) := continuous_abs.measurable
    exact (habs.mul hf.1).mul hg
  apply h.mono hm.aestronglyMeasurable
  filter_upwards [hR.2] with u hu
  by_cases hmem : u ∈ Icc (-R) R
  · have hRu := abs_le.mpr hmem
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hR.1, abs_of_nonneg hC₀]
    calc
      |u| * |f u| * |g u| ≤ R * |f u| * C :=
        mul_le_mul (mul_le_mul_of_nonneg_right hRu (abs_nonneg _)) (hC u)
          (abs_nonneg _) (mul_nonneg hR.1 (abs_nonneg _))
      _ = R * C * |f u| := by ring
  · simp [hu hmem]

private theorem weighted_product_l1_tendsto {f g : FourierProfile} {F G : ℕ → FourierProfile}
    (hf : IsProfile f) (hg : IsProfile g) (hF : ∀ n, IsProfile (F n))
    (hG : ∀ n, IsProfile (G n)) {R C : ℝ} (hR : HasRadiusAtMost f R)
    (hFR : ∀ n, HasRadiusAtMost (F n) R) (hC₀ : 0 ≤ C) (hC : ∀ n u, |G n u| ≤ C)
    (hFl : Tendsto (fun n => profileL1 (F n - f)) atTop (𝓝 0))
    (hGl : Tendsto (fun n => profileL1 (G n - g)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u : ℝ, |u| * F n u * G n u)
      atTop (𝓝 (∫ u : ℝ, |u| * f u * g u)) := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hf.2.2.1
  have hM' (u : ℝ) : |f u| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM (f u) ⟨u, rfl⟩
  have hM₀ : 0 ≤ M := (abs_nonneg (f 0)).trans (hM' _)
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp hg.2.2.1
  have hD' (u : ℝ) : |g u| ≤ D := by
    simpa only [Real.norm_eq_abs] using hD (g u) ⟨u, rfl⟩
  have hI := integrable_weighted_product hf hg.1 hR ((abs_nonneg (g 0)).trans (hD' 0)) hD'
  have hIF (n : ℕ) := integrable_weighted_product (hF n) (hG n).1 (hFR n) hC₀ (hC n)
  have hlim : Tendsto (fun n => R * C * profileL1 (F n - f) +
      R * M * profileL1 (G n - g)) atTop (𝓝 0) := by
    simpa using (hFl.const_mul (R * C)).add (hGl.const_mul (R * M))
  have hLp : Tendsto (fun n => profileL1 ((fun u : ℝ => |u| * F n u * G n u) -
      (fun u : ℝ => |u| * f u * g u))) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => profileL1_nonneg _) (fun n => ?_) hlim
    unfold profileL1
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (((integrable_of_isProfile (hF n)).sub (integrable_of_isProfile hf)).abs.const_mul _)
        (((integrable_of_isProfile (hG n)).sub (integrable_of_isProfile hg)).abs.const_mul _)]
    apply integral_mono_ae ((hIF n).sub hI).abs
      ((((integrable_of_isProfile (hF n)).sub (integrable_of_isProfile hf)).abs.const_mul _).add
        (((integrable_of_isProfile (hG n)).sub (integrable_of_isProfile hg)).abs.const_mul _))
    filter_upwards [hR.2, (hFR n).2] with u hu huF
    simp only [Pi.sub_apply, Pi.add_apply]
    by_cases hmem : u ∈ Icc (-R) R
    · have habs := abs_le.mpr hmem
      rw [show |u| * F n u * G n u - |u| * f u * g u =
        |u| * ((F n u - f u) * G n u) + |u| * (f u * (G n u - g u)) by ring]
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul, abs_abs]
      calc
        _ ≤ R * (C * |F n u - f u|) + R * (M * |G n u - g u|) := by
          rw [mul_comm |F n u - f u| |G n u|]
          apply add_le_add
          · exact mul_le_mul habs (mul_le_mul_of_nonneg_right (hC n u) (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hR.1
          · exact mul_le_mul habs (mul_le_mul_of_nonneg_right (hM' u) (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hR.1
        _ = _ := by ring
    · simp only [hu hmem, huF hmem, mul_zero, zero_mul, sub_self, abs_zero, zero_add]
      exact mul_nonneg (mul_nonneg hR.1 hM₀) (abs_nonneg _)
  simpa only [Measure.restrict_univ] using integral_tendsto_of_profileL1 Set.univ hI hIF hLp

def UniformProfileBounds {n : ℕ} (hs : ℕ → Fin n → FourierProfile) (h : Fin n → FourierProfile) :
    Prop :=
  (∀ i, IsProfile (h i)) ∧ (∀ j i, IsProfile (hs j i)) ∧
    ∃ M R : ℝ, 0 ≤ M ∧ 0 ≤ R ∧
      (∀ j i u, |hs j i u| ≤ M) ∧
      (∀ j i, HasRadiusAtMost (hs j i) R) ∧
      (∀ i, HasRadiusAtMost (h i) R)

/-- Lemma 6(d). Restricted cumulants are continuous under the stated profile convergence. -/
theorem cumulant_continuity {n : ℕ} (hs : ℕ → Fin n → FourierProfile) (h : Fin n → FourierProfile)
    (hb : UniformProfileBounds hs h)
    (hl : ∀ i, Tendsto (fun j => profileL1 (hs j i - h i)) atTop (𝓝 0))
    (hzero : n = 1 → ∀ i, Tendsto (fun j => hs j i 0) atTop (𝓝 (h i 0))) :
    Tendsto (fun j => delta (List.ofFn (hs j))) atTop (𝓝 (delta (List.ofFn h))) ∧
      Tendsto (fun j => cumulant (List.ofFn (hs j))) atTop (𝓝 (cumulant (List.ofFn h))) := by
  obtain ⟨hh, hhs, M, R, hM₀, _, hM, hR, hhR⟩ := hb
  have hd := delta_continuity hs h hhs hh hl
  refine ⟨hd, ?_⟩
  rcases n with _ | _ | _ | n
  · simp [List.ofFn_zero, cumulant]
  · have hi := integral_tendsto_of_profileL1 (Ioc (0 : ℝ) 1) (integrable_of_isProfile (hh 0))
      (fun j => integrable_of_isProfile (hhs j 0)) (hl 0)
    have hfinal := (hzero rfl 0).sub hi
    simpa only [List.ofFn_succ, List.ofFn_zero, cumulant, intervalIntegral.integral_of_le zero_le_one] using hfinal
  · have hi := weighted_product_l1_tendsto (hh 0) (hh 1)
      (fun j => hhs j 0) (fun j => hhs j 1) (hhR 0) (fun j => hR j 0)
      hM₀ (fun j => hM j 1) (hl 0) (hl 1)
    have hfinal := (hi.const_mul 2).add hd
    simpa only [List.ofFn_succ, List.ofFn_zero, cumulant] using hfinal
  · simpa only [List.ofFn_succ, cumulant] using hd

end Chowla
