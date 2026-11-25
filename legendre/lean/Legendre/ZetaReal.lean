import Legendre.ZetaZeros
import Mathlib.Analysis.Real.Pi.Bounds

namespace Legendre

open Complex MeasureTheory Set

private theorem theta_tail_bound {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ HurwitzZeta.evenKernel 0 t - 1 ∧ HurwitzZeta.evenKernel 0 t - 1 ≤ 2 / t ^ 2 := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hπ : 2 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  let q := Real.exp (-2 * t)
  have hq₀ : 0 ≤ q := (Real.exp_pos _).le
  have hqt : q ≤ 1 / (2 * t ^ 2) := by
    have hexp := Real.pow_div_factorial_le_exp (x := 2 * t) (by positivity) 2
    have hexp' : 2 * t ^ 2 ≤ Real.exp (2 * t) := by norm_num at hexp; nlinarith
    change Real.exp (-2 * t) ≤ _
    rw [neg_mul, Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) hexp'
  have hq : q ≤ 1 / 2 := hqt.trans (by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith only [ht, mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ t + 1 by positivity)])
  have hsum : HasSum (fun n : ℕ ↦ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))
      (HurwitzZeta.evenKernel 0 t - 1) := by
    rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
    simpa using HurwitzZeta.hasSum_nat_cosKernel₀ 0 ht₀
  constructor
  · rw [← hsum.tsum_eq]
    exact tsum_nonneg (fun _ ↦ by positivity)
  · have hgeo := ((hasSum_geometric_of_lt_one hq₀ (hq.trans_lt (by norm_num))).mul_left (2 * q))
    have hcompare : HurwitzZeta.evenKernel 0 t - 1 ≤ (2 * q) * (1 - q)⁻¹ := by
      rw [← hsum.tsum_eq, ← hgeo.tsum_eq]
      apply hsum.summable.tsum_le_tsum _ hgeo.summable
      intro n
      rw [show 2 * q * q ^ n = 2 * q ^ (n + 1) by rw [pow_succ]; ring]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      change Real.exp _ ≤ Real.exp (-2 * t) ^ (n + 1)
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hn : 1 ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
      have hn' : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ (n : ℝ) + 1 by positivity)]
      have hle : 2 * ((n : ℝ) + 1) ≤ Real.pi * ((n : ℝ) + 1) ^ 2 := by
        exact (mul_le_mul_of_nonneg_left hn' (by norm_num)).trans
          (mul_le_mul_of_nonneg_right hπ (sq_nonneg _))
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_right hle ht₀.le]
    have hInv : (1 - q)⁻¹ ≤ 2 := by
      have hp : 0 < 1 - q := by linarith
      rw [inv_eq_one_div, div_le_iff₀ hp]
      linarith
    calc
      _ ≤ (2 * q) * (1 - q)⁻¹ := hcompare
      _ ≤ (2 * q) * 2 := mul_le_mul_of_nonneg_left hInv (by positivity)
      _ ≤ 2 / t ^ 2 := by linarith only [hqt, show 4 * (1 / (2 * t ^ 2)) = 2 / t ^ 2 by ring]

private noncomputable def thetaPair : WeakFEPair ℂ := HurwitzZeta.hurwitzEvenFEPair 0

private noncomputable def centralMellinTerm (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • thetaPair.f_modif t

private theorem thetaPair_g_modif (t : ℝ) (ht : 1 < t) :
    thetaPair.g_modif t = (HurwitzZeta.evenKernel 0 t - 1 : ℝ) := by
  rw [WeakFEPair.g_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr ht),
    indicator_of_notMem (notMem_Ioo_of_ge ht.le), add_zero]
  simp [thetaPair, HurwitzZeta.hurwitzEvenFEPair, HurwitzZeta.evenKernel_eq_cosKernel_of_zero]

private theorem centralMellinTerm_high {t : ℝ} (ht : 1 < t) : ‖centralMellinTerm t‖ ≤ 2 / t ^ 2 := by
  have ht₀ := zero_lt_one.trans ht
  have htail := theta_tail_bound ht.le
  rw [centralMellinTerm, norm_smul, norm_cpow_eq_rpow_re_of_pos ht₀, WeakFEPair.f_modif,
    Pi.add_apply, indicator_of_mem (mem_Ioi.mpr ht),
    indicator_of_notMem (notMem_Ioo_of_ge ht.le), add_zero]
  simp only [thetaPair, HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, if_true]
  rw [← Complex.ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_nonneg htail.1]
  have hp : t ^ ((1 / 4 : ℂ) - 1).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht.le (by norm_num [Complex.div_re])
  exact (mul_le_mul_of_nonneg_right hp htail.1).trans (by simpa only [one_mul] using htail.2)

private theorem centralMellinTerm_low {t : ℝ} (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    ‖centralMellinTerm t‖ ≤ 2 := by
  rcases ht₁.eq_or_lt with rfl | ht₁
  · simp [centralMellinTerm, WeakFEPair.f_modif]
  have hi := one_div_pos.mpr ht₀
  have hti : 1 < 1 / t := (lt_div_iff₀ ht₀).mpr (by simpa using ht₁)
  have hfe := thetaPair.hf_modif_FE (1 / t) hi
  rw [one_div_one_div] at hfe
  have hf : thetaPair.f_modif t =
      (((1 / t) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((HurwitzZeta.evenKernel 0 (1 / t) - 1 : ℝ) : ℂ) := by
    rw [thetaPair_g_modif _ hti] at hfe
    simpa [thetaPair, HurwitzZeta.hurwitzEvenFEPair] using hfe
  have htail := theta_tail_bound hti.le
  have htail' : HurwitzZeta.evenKernel 0 (1 / t) - 1 ≤ 2 * t ^ 2 := by
    convert htail.2 using 1
    field_simp [ht₀.ne']
  have hinv : (1 / t : ℝ) ^ (1 / 2 : ℝ) ≤ t⁻¹ := by
    rw [one_div]
    convert Real.rpow_le_rpow_of_exponent_le (show 1 ≤ t⁻¹ by simpa [one_div] using hti.le)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) using 1
    exact (Real.rpow_one _).symm
  have hpow : t ^ ((1 / 4 : ℂ) - 1).re ≤ t⁻¹ := by
    rw [← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_ge ht₀ ht₁.le
    norm_num [Complex.div_re]
  rw [centralMellinTerm, norm_smul, norm_cpow_eq_rpow_re_of_pos ht₀, hf, norm_mul,
    norm_real, norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg htail.1]
  calc
    _ ≤ t⁻¹ * (t⁻¹ * (2 * t ^ 2)) := by
      exact mul_le_mul hpow
        (mul_le_mul hinv htail' htail.1 (inv_nonneg.mpr ht₀.le))
        (mul_nonneg (Real.rpow_nonneg hi.le _) htail.1) (inv_nonneg.mpr ht₀.le)
    _ = 2 := by field_simp [ht₀.ne']

private theorem completedZeta₀_half_norm : ‖completedRiemannZeta₀ (1 / 2)‖ ≤ 2 := by
  have hc : IntegrableOn centralMellinTerm (Ioi 0) :=
    (thetaPair.toStrongFEPair.hasMellin (1 / 4)).1
  have hcn : IntegrableOn (fun t ↦ ‖centralMellinTerm t‖) (Ioi 0) := hc.norm
  have unc : ‖∫ t in Ioi (0 : ℝ), centralMellinTerm t‖ ≤ 4 := by
    apply (norm_integral_le_integral_norm _).trans
    have hd : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := disjoint_left.mpr fun _ hx hy ↦ hy.not_ge hx.2
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
      setIntegral_union hd measurableSet_Ioi (hcn.mono_set Ioc_subset_Ioi_self)
        (hcn.mono_set (Ioi_subset_Ioi (by norm_num)))]
    have hlow : (∫ t in Ioc (0 : ℝ) 1, ‖centralMellinTerm t‖) ≤ 2 := by
      apply (setIntegral_mono_on (hcn.mono_set Ioc_subset_Ioi_self)
        (integrableOn_const (by simp)) measurableSet_Ioc fun t ht ↦
          centralMellinTerm_low ht.1 ht.2).trans
      simp [Real.volume_real_Ioc]
    have hId : ∀ t ∈ Ioi (1 : ℝ), (2 / t ^ 2 : ℝ) = 2 * t ^ (-2 : ℝ) := by
      intro t ht
      rw [Real.rpow_neg (zero_lt_one.trans ht).le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      ring
    have hpower := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul 2
    have hhigh : (∫ t in Ioi (1 : ℝ), ‖centralMellinTerm t‖) ≤ 2 := by
      apply (setIntegral_mono_on (hcn.mono_set (Ioi_subset_Ioi (by norm_num)))
        hpower measurableSet_Ioi (fun t ht ↦ (centralMellinTerm_high ht).trans_eq (hId t ht))).trans
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
      norm_num
    linarith
  change ‖thetaPair.Λ₀ ((1 / 2 : ℂ) / 2) / 2‖ ≤ 2
  rw [show (1 / 2 : ℂ) / 2 = 1 / 4 by ring, WeakFEPair.Λ₀, mellin, norm_div, Complex.norm_two]
  change ‖∫ t in Ioi (0 : ℝ), centralMellinTerm t‖ / 2 ≤ 2
  linarith only [unc]

/-- The centre of the critical strip is not a zero. The completed theta integral has norm at most
`2`, while the two polar terms at `1/2` sum to `4`. -/
theorem riemannZeta_half_ne_zero : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  intro hζ
  have hz : (1 / 2 : ℂ) ≠ 0 := by norm_num
  rw [riemannZeta_def_of_ne_zero hz, div_eq_zero_iff] at hζ
  have hΛ := hζ.resolve_right (Gammaℝ_ne_zero_of_re_pos (by norm_num [Complex.div_re]))
  rw [completedRiemannZeta_eq, show (1 - 1 / 2 : ℂ) = 1 / 2 by ring,
    show (1 / (1 / 2) : ℂ) = 2 by norm_num] at hΛ
  have hΛ' : completedRiemannZeta₀ (1 / 2) = 4 := by linear_combination hΛ
  have hn := completedZeta₀_half_norm
  rw [hΛ', Complex.norm_ofNat 4] at hn
  norm_num at hn

/-- Under RH, no nontrivial zero has ordinate zero. -/
theorem nontrivialZero_im_ne_zero_of_RH (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZeros) : ρ.im ≠ 0 := by
  intro him
  have hr := nontrivialZero_re_of_RH hRH hρ
  have hz : ρ = 1 / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, hr, him]
  exact riemannZeta_half_ne_zero (hz ▸ hρ.2.2)

end Legendre
