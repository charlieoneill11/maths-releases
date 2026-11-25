import Legendre.Cosine
import Legendre.Geometry
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Legendre

open MeasureTheory Set
open scoped BigOperators

private theorem window_width_tiny (w : Window) (K : ℝ) (hw : WindowBounds w K) :
    K * w.D ≤ (1 / 10 ^ 12 : ℝ) :=
  hw.width.trans (by norm_num [U])

private theorem window_D_lt_one (w : Window) (K : ℝ) (hw : WindowBounds w K) (hK : 1 ≤ K) :
    w.D < 1 := by
  have h := mul_le_mul_of_nonneg_right hK hw.D_pos.le
  linarith only [h, window_width_tiny w K hw]

private theorem log_window_endpoint (w : Window) (ha : 0 < w.a) (s : ℝ) :
    Real.log (w.endpoint s) = Real.log w.a + w.D * s := by
  rw [Window.endpoint, Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp]

private theorem abs_one_sub_cosh_le_sq {t : ℝ} (ht : |t| ≤ 1) :
    |1 - Real.cosh t| ≤ t ^ 2 := by
  have hcosh : 1 ≤ Real.cosh t := by
    rw [Real.cosh_eq]
    linarith only [Real.add_one_le_exp t, Real.add_one_le_exp (-t)]
  rw [abs_of_nonpos (sub_nonpos.mpr hcosh)]
  have h₁ := (le_abs_self (Real.exp t - 1 - t)).trans (Real.abs_exp_sub_one_sub_id_le ht)
  have h₂ := (le_abs_self (Real.exp (-t) - 1 - (-t))).trans
    (Real.abs_exp_sub_one_sub_id_le (by simpa only [abs_neg] using ht))
  rw [Real.cosh_eq]
  nlinarith only [h₁, h₂]

/-- The pole term in Proposition 17 differs below from `P F(0)` by at most `10⁻²²`. -/
theorem gap_pole_lower (w : Window) (g : CosineTest) (hw : WindowBounds w g.K)
    (hK : 1 ≤ g.K) (hmass : g.mass < 4) :
    w.P * g.F 0 ≤ poleTerm w g + 1 / 10 ^ 22 := by
  let c : ℝ := (g.K * w.D / 2) ^ 2
  let f : ℝ → ℝ := fun s ↦ g.polynomial s * Real.cosh (w.D * s / 2)
  let d : ℝ → ℝ := fun s ↦ |g.polynomial s| * c
  have hP : 0 ≤ w.P := mul_nonneg hw.D_pos.le (Real.sqrt_nonneg _)
  have hP' : w.P ≤ 100 := by
    have h := mul_le_mul_of_nonneg_right hK hP
    linarith only [h, hw.scale]
  have hab : -g.K ≤ g.K := by linarith only [g.K_pos]
  have hfc : Continuous f := g.continuous_polynomial.mul (Real.continuous_cosh.comp (by fun_prop))
  have hdc : Continuous d := g.continuous_polynomial.abs.mul continuous_const
  have hsmall := window_width_tiny w g.K hw
  have hpoint (s : ℝ) (hs : s ∈ Icc (-g.K) g.K) : g.polynomial s ≤ f s + d s := by
    have hscale : |w.D * s / 2| ≤ g.K * w.D / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul, abs_of_pos hw.D_pos]
      have h := mul_le_mul_of_nonneg_left (abs_le.mpr hs) hw.D_pos.le
      linarith only [h]
    have hunit : |w.D * s / 2| ≤ 1 := by linarith only [hsmall, hscale]
    have hsquare : (w.D * s / 2) ^ 2 ≤ c := by
      rw [← sq_abs (w.D * s / 2)]
      exact pow_le_pow_left₀ (abs_nonneg _) hscale _
    have habs := (abs_one_sub_cosh_le_sq hunit).trans hsquare
    have hprod : g.polynomial s * (1 - Real.cosh (w.D * s / 2)) ≤ |g.polynomial s| * c := by
      calc
        _ ≤ |g.polynomial s * (1 - Real.cosh (w.D * s / 2))| := le_abs_self _
        _ = |g.polynomial s| * |1 - Real.cosh (w.D * s / 2)| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    dsimp [f, d]
    linarith only [hprod]
  have hint : (∫ s in -g.K..g.K, g.polynomial s) ≤ ∫ s in -g.K..g.K, f s + d s :=
    intervalIntegral.integral_mono_on hab (g.continuous_polynomial.intervalIntegrable _ _)
      ((hfc.add hdc).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_add (hfc.intervalIntegrable _ _) (hdc.intervalIntegrable _ _),
    show d = fun s ↦ |g.polynomial s| * c by rfl, intervalIntegral.integral_mul_const,
    ← g.mass_eq_interval] at hint
  have hF : g.F 0 ≤ (∫ s in -g.K..g.K, f s) + g.mass * c := by
    simpa only [CosineTest.F, mul_zero, zero_mul, Real.cos_zero, mul_one] using hint
  have hcn : 0 ≤ c := sq_nonneg _
  have hcu : c ≤ (1 / 10 ^ 12 / 2 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (div_nonneg (mul_nonneg g.K_pos.le hw.D_pos.le) (by norm_num))
      (by linarith only [hsmall]) 2
  have hmC : g.mass * c ≤ 4 * ((1 / 10 ^ 12 / 2 : ℝ) ^ 2) :=
    mul_le_mul hmass.le hcu hcn (by norm_num)
  have herror : w.P * (g.mass * c) ≤ (1 / 10 ^ 22 : ℝ) := by
    calc
      _ ≤ 100 * (4 * ((1 / 10 ^ 12 / 2 : ℝ) ^ 2)) :=
        (mul_le_mul_of_nonneg_left hmC hP).trans
          (mul_le_mul_of_nonneg_right hP' (by norm_num))
      _ = _ := by norm_num
  have hmain := mul_le_mul_of_nonneg_left hF hP
  change w.P * g.F 0 ≤ w.P * (∫ s in -g.K..g.K, f s) + 1 / 10 ^ 22
  linarith only [hmain, herror]

private theorem gap_support_lower (w : Window) (K : ℝ) (hw : WindowBounds w K) :
    (10 : ℝ) ^ 12 ≤ w.endpoint (-K) := by
  have ha : Real.exp 60 ≤ w.a := (Real.le_log_iff_exp_le hw.a_pos).mp hw.log_a
  have ha₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le 60
  rw [Real.exp_one_pow] at ha₂
  have hA : w.a / U ≤ w.endpoint (-K) := by
    rw [Window.endpoint, mul_neg, mul_comm w.D K, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (window_exp_lower hw.width) hw.a_pos.le
  exact (show (10 : ℝ)^12 ≤ 2^60 / U by norm_num [U]).trans <|
    (div_le_div_of_nonneg_right (ha₂.trans ha) (by norm_num [U])).trans hA

private theorem trivial_zero_term_bound (w : Window) (g : CosineTest)
    (hw : WindowBounds w g.K) (hmass : g.mass < 4) (k : ℕ) :
    |trivialZeroTerm w g k| ≤ 4 * (1 / 10 ^ 24 : ℝ) ^ (k + 1) := by
  let A := w.endpoint (-g.K)
  let r := 2 * ((k : ℝ) + 1) + 1 / 2
  let C := Real.exp (r * w.D * g.K)
  have ha : (10 : ℝ) ^ 12 ≤ A := gap_support_lower w g.K hw
  have ha₀ : 0 < A := by linarith only [ha]
  have ha₁ : 1 ≤ A := by linarith only [ha]
  have hr : 0 < r := by dsimp [r]; positivity
  have hab : -g.K ≤ g.K := by linarith only [g.K_pos]
  have hi (s : ℝ) (hs : s ∈ Icc (-g.K) g.K) :
      |g.polynomial s * Real.exp (-r * w.D * s)| ≤ |g.polynomial s| * C := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hs.1 (mul_nonneg hr.le hw.D_pos.le)
    linarith only [hm]
  have hcont : Continuous fun s ↦ (g.polynomial s * Real.exp (-r * w.D * s)) :=
    g.continuous_polynomial.mul (Real.continuous_exp.comp (by fun_prop))
  have hint : |∫ s in -g.K..g.K, g.polynomial s * Real.exp (-r * w.D * s)| ≤ g.mass * C := by
    apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
    rw [g.mass_eq_interval, ← intervalIntegral.integral_mul_const]
    exact intervalIntegral.integral_mono_on hab (hcont.abs.intervalIntegrable _ _)
      ((g.continuous_polynomial.abs.mul continuous_const).intervalIntegrable _ _) hi
  have heq : w.a ^ (-r) * C = A ^ (-r) := by
    rw [Real.rpow_def_of_pos hw.a_pos, Real.rpow_def_of_pos ha₀]
    dsimp [A, C]
    rw [log_window_endpoint w hw.a_pos, ← Real.exp_add]
    congr 1
    ring
  have hrpow : A ^ (-r) ≤ ((10 : ℝ) ^ 12) ^ (-(2 * ((k : ℝ) + 1))) := by
    calc
      _ ≤ A ^ (-(2 * ((k : ℝ) + 1))) :=
        Real.rpow_le_rpow_of_exponent_le ha₁ (by dsimp [r]; linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) ha (neg_nonpos.mpr (by positivity))
  have hqpow : ((10 : ℝ) ^ 12) ^ (-(2 * ((k : ℝ) + 1))) = (1 / 10 ^ 24 : ℝ) ^ (k + 1) := by
    rw [Real.rpow_neg (by positivity), show (2 : ℝ) * ((k : ℝ) + 1) = ((2 * (k + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul, ← inv_pow]
    norm_num
  calc
    |trivialZeroTerm w g k| = w.a ^ (-r) * |∫ s in -g.K..g.K, g.polynomial s * Real.exp (-r * w.D * s)| := by
      rw [trivialZeroTerm, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hw.a_pos _)]
    _ ≤ w.a ^ (-r) * (g.mass * C) := mul_le_mul_of_nonneg_left hint (Real.rpow_nonneg hw.a_pos.le _)
    _ = g.mass * (w.a ^ (-r) * C) := by ring
    _ ≤ 4 * (A ^ (-r)) := by rw [heq]; exact mul_le_mul_of_nonneg_right hmass.le (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hrpow.trans_eq hqpow) (by norm_num)

/-- The contribution from the trivial zeros in Proposition 17. -/
theorem gap_trivial_zeros (w : Window) (g : CosineTest) (hw : WindowBounds w g.K)
    (hK : 1 ≤ g.K) (hmass : g.mass < 4) : Summable (trivialZeroTerm w g) ∧
    |w.D * (∑' k : ℕ, trivialZeroTerm w g k)| < 1 / 10 ^ 20 := by
  let q : ℝ := 1 / 10 ^ 24
  have hq₀ : 0 ≤ q := by norm_num [q]
  have hq₁ : q < 1 := by norm_num [q]
  have hsq : Summable (fun k : ℕ ↦ (4 * q) * q ^ k) :=
    (summable_geometric_of_lt_one hq₀ hq₁).mul_left (4 * q)
  have hnorm (k : ℕ) : ‖trivialZeroTerm w g k‖ ≤ (4 * q) * q ^ k := by
    rw [Real.norm_eq_abs, mul_assoc, ← pow_succ']
    exact trivial_zero_term_bound w g hw hmass k
  have hsum : Summable (trivialZeroTerm w g) := Summable.of_norm_bounded hsq hnorm
  have hnormsum : Summable (fun k : ℕ ↦ ‖trivialZeroTerm w g k‖) :=
    Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hnorm hsq
  have htsum : |∑' k : ℕ, trivialZeroTerm w g k| ≤ (4 * q) * (1 - q)⁻¹ := by
    rw [← Real.norm_eq_abs]
    apply (norm_tsum_le_tsum_norm hnormsum).trans
    have hbound := hnormsum.tsum_le_tsum hnorm hsq
    rwa [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁] at hbound
  refine ⟨hsum, ?_⟩
  rw [abs_mul, abs_of_pos hw.D_pos]
  calc
    _ ≤ 1 * |∑' k : ℕ, trivialZeroTerm w g k| :=
      mul_le_mul_of_nonneg_right (window_D_lt_one w g.K hw hK).le (abs_nonneg _)
    _ ≤ (4 * q) * (1 - q)⁻¹ := by simpa only [one_mul] using htsum
    _ < _ := by norm_num [q]

private theorem endpoint_sqrt (w : Window) (ha : 0 < w.a) (s : ℝ) :
    Real.sqrt (w.endpoint s) = Real.sqrt w.a * Real.exp (w.D * s / 2) := by
  rw [Window.endpoint, Real.sqrt_mul ha.le, Real.sqrt_eq_rpow (Real.exp _),
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 2
  ring

private theorem sqrt_support_width (w : Window) (K : ℝ) (hw : WindowBounds w K)
    (hK : 0 ≤ K) :
    Real.sqrt (w.endpoint K) - Real.sqrt (w.endpoint (-K)) ≤ K * w.P * U := by
  let t := w.D * K / 2
  have ht : 0 ≤ t := div_nonneg (mul_nonneg hw.D_pos.le hK) (by norm_num)
  have ht' : t ≤ (U - 1) / U := by
    have h := mul_nonneg hK hw.D_pos.le
    dsimp [t]
    linarith only [hw.width, h]
  have hexp := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t - t)) (Real.exp_pos t).le
  rw [← Real.exp_add, sub_add_cancel] at hexp
  have hdiff : Real.exp t - Real.exp (-t) ≤ 2 * t * U := by
    have h₁ : Real.exp t - Real.exp (-t) ≤ 2 * t * Real.exp t := by linarith only [hexp]
    exact h₁.trans (mul_le_mul_of_nonneg_left (window_exp_upper ht') (by positivity))
  rw [endpoint_sqrt w hw.a_pos, endpoint_sqrt w hw.a_pos, show w.D * (-K) / 2 = -t by
    dsimp [t]; ring]
  unfold Window.P
  have hs := mul_le_mul_of_nonneg_left hdiff (Real.sqrt_nonneg w.a)
  dsimp [t] at hs
  linarith only [hs]

private theorem root_width_le_sqrt_width {a b c : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hc₀ : 0 ≤ c) (hc : c ≤ 1 / 2) :
    b ^ c - a ^ c ≤ Real.sqrt b - Real.sqrt a := by
  let f : ℝ → ℝ := fun t ↦ t ^ ((1 : ℝ) / 2) - t ^ c
  have hf : Continuous f := (Real.continuous_rpow_const (by norm_num)).sub
    (Real.continuous_rpow_const hc₀)
  have hderiv (t : ℝ) (ht : t ∈ interior (Ici (1 : ℝ))) :
      HasDerivAt f ((1 / 2) * t ^ ((1 / 2 : ℝ) - 1) - c * t ^ (c - 1)) t := by
    rw [interior_Ici] at ht
    have ht' : t ≠ 0 := by have h : 1 < t := ht; linarith
    exact (Real.hasDerivAt_rpow_const (Or.inl ht')).sub (Real.hasDerivAt_rpow_const (Or.inl ht'))
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (1 : ℝ)) hf.continuousOn
    (fun t ht ↦ (hderiv t ht).differentiableAt.differentiableWithinAt) (fun t ht ↦ by
      rw [(hderiv t ht).deriv]
      rw [interior_Ici] at ht
      have ht' : 1 ≤ t := (show 1 < t from ht).le
      have hs : t ^ (c - 1) ≤ t ^ ((1 / 2 : ℝ) - 1) :=
        Real.rpow_le_rpow_of_exponent_le ht' (sub_le_sub_right hc 1)
      exact sub_nonneg.mpr (mul_le_mul hc hs (Real.rpow_nonneg (zero_le_one.trans ht') _) (by norm_num)))
  have hh := hm (show a ∈ Ici (1 : ℝ) from ha) (show b ∈ Ici (1 : ℝ) from ha.trans hab) hab
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  dsimp [f] at hh
  linarith only [hh]

private theorem nat_Icc_card_le_real_width {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) ≤ 1 + b - a := by
  rw [Nat.card_Icc]
  by_cases h : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1
  · rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one]
    linarith only [Nat.floor_le (ha.trans hab), Nat.le_ceil a]
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero]
    linarith only [hab]

private theorem proper_prime_power_count (w : Window) (K : ℝ) (hw : WindowBounds w K)
    (hK : 0 ≤ K) {powers : Finset ℕ}
    (hmem : ∀ m ∈ powers, ¬m.Prime ∧ IsPrimePow m ∧ w.endpoint (-K) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ w.endpoint K) :
    (powers.card : ℝ) ≤ ((Real.log w.a + K * w.D) / Real.log 2) * (1 + K * w.P * U) := by
  classical
  let A := w.endpoint (-K)
  let B := w.endpoint K
  let ell := Real.log w.a + K * w.D
  let exponents := Finset.Icc 2 ⌊ell / Real.log 2⌋₊
  let root (r : ℕ) (t : ℝ) := t ^ ((1 : ℝ) / (r : ℝ))
  let bases (r : ℕ) := Finset.Icc ⌈root r A⌉₊ ⌊root r B⌋₊
  let powersAt (r : ℕ) := (bases r).image (fun m ↦ m ^ r)
  have hAB : A ≤ B := (w.endpoint_strictMono hw.a_pos hw.D_pos).monotone (by linarith)
  have hA : 1 ≤ A := (by norm_num : (1 : ℝ) ≤ 2).trans (window_lower_support w K hw)
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hB₀ : 0 ≤ B := hA₀.trans hAB
  have hell : 0 ≤ ell := by dsimp [ell]; linarith only [hw.log_a, mul_nonneg hK hw.D_pos.le]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : Real.log B = ell := by
    dsimp [B, ell]
    rw [log_window_endpoint w hw.a_pos, mul_comm w.D]
  have hcut₀ : 0 ≤ ell / Real.log 2 := div_nonneg hell hlog2.le
  have hset : powers ⊆ exponents.biUnion powersAt := by
    intro m hm
    obtain ⟨hmprime, hmPower, hmA, hmB⟩ := hmem m hm
    obtain ⟨p, r, hp, hr, hpow⟩ := (isPrimePow_nat_iff m).1 hmPower
    have hr₂ : 2 ≤ r := by
      by_contra! hh
      have h₁ : r = 1 := by omega
      have heq : p = m := by simpa [h₁] using hpow
      exact hmprime (heq ▸ hp)
    have hr₀ : 0 < (r : ℝ) := by exact_mod_cast hr
    have hpc : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpowC : (p : ℝ) ^ r = (m : ℝ) := by exact_mod_cast hpow
    have hlogm := (Real.log_le_log (by exact_mod_cast (zero_lt_one.trans hmPower.one_lt)) hmB).trans_eq hlogB
    rw [← hpowC, Real.log_pow] at hlogm
    have hr_le : (r : ℝ) ≤ ell / Real.log 2 := by
      apply (le_div_iff₀ hlog2).2
      exact (mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hpc) hr₀.le).trans hlogm
    have hroot_pos : 0 < (1 : ℝ) / r := one_div_pos.mpr hr₀
    have hrootEq : (m : ℝ) ^ ((1 : ℝ) / (r : ℝ)) = (p : ℝ) := by
      rw [← hpowC, ← Real.rpow_natCast_mul (Nat.cast_nonneg p), show (r : ℝ) * (1 / r) = 1 by
        field_simp, Real.rpow_one]
    have hbase : p ∈ bases r := by
      have h₁ := (Real.rpow_le_rpow hA₀ hmA hroot_pos.le).trans_eq hrootEq
      have h₂ := hrootEq.symm.trans_le (Real.rpow_le_rpow (Nat.cast_nonneg m) hmB hroot_pos.le)
      exact Finset.mem_Icc.2 ⟨Nat.ceil_le.2 h₁,
        (Nat.le_floor_iff (Real.rpow_nonneg hB₀ _)).2 h₂⟩
    have hexp : r ∈ exponents := Finset.mem_Icc.2 ⟨hr₂, (Nat.le_floor_iff hcut₀).2 hr_le⟩
    exact Finset.mem_biUnion.2 ⟨r, hexp, Finset.mem_image.2 ⟨p, hbase, hpow⟩⟩
  have hcard_exp : (exponents.card : ℝ) ≤ ell / Real.log 2 := by
    have hn : exponents.card ≤ ⌊ell / Real.log 2⌋₊ := by dsimp [exponents]; rw [Nat.card_Icc]; omega
    exact (show (exponents.card : ℝ) ≤ (⌊ell / Real.log 2⌋₊ : ℝ) by exact_mod_cast hn).trans
      (Nat.floor_le hcut₀)
  have hbase_width (r : ℕ) (hr : r ∈ exponents) : ((bases r).card : ℝ) ≤ 1 + K * w.P * U := by
    have hr₂ : (2 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.1 hr).1
    have hr₀ : (0 : ℝ) < r := by linarith only [hr₂]
    have hroot₀ : 0 ≤ (1 : ℝ) / r := one_div_nonneg.mpr hr₀.le
    have hroot₁ : (1 : ℝ) / r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hr₂
    have hc := nat_Icc_card_le_real_width (Real.rpow_nonneg hA₀ ((1 : ℝ) / r))
      (Real.rpow_le_rpow hA₀ hAB hroot₀)
    have hh := root_width_le_sqrt_width hA hAB hroot₀ hroot₁
    have hs := sqrt_support_width w K hw hK
    change ((bases r).card : ℝ) ≤ _
    exact hc.trans (by linarith only [hh, hs])
  have hn : 0 ≤ 1 + K * w.P * U := by
    have hP : 0 ≤ w.P := mul_nonneg hw.D_pos.le (Real.sqrt_nonneg _)
    have hU : 0 ≤ U := by norm_num [U]
    positivity
  calc
    (powers.card : ℝ) ≤ ((exponents.biUnion powersAt).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hset
    _ ≤ (∑ r ∈ exponents, (powersAt r).card : ℕ) := by exact_mod_cast Finset.card_biUnion_le
    _ = ∑ r ∈ exponents, ((powersAt r).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _r ∈ exponents, (1 + K * w.P * U) := Finset.sum_le_sum (fun r hr ↦
      (show ((powersAt r).card : ℝ) ≤ ((bases r).card : ℝ) by exact_mod_cast Finset.card_image_le).trans
        (hbase_width r hr))
    _ = (exponents.card : ℝ) * (1 + K * w.P * U) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard_exp hn

private theorem mangoldt_weight_bound (w : Window) (K : ℝ) (hw : WindowBounds w K)
    {m : ℕ} (hmA : w.endpoint (-K) ≤ (m : ℝ)) (hmB : (m : ℝ) ≤ w.endpoint K) :
    ArithmeticFunction.vonMangoldt m / Real.sqrt (m : ℝ) ≤
      (Real.log w.a + K * w.D) * U / Real.sqrt w.a := by
  have hm₀ : (0 : ℝ) < m := (w.endpoint_pos hw.a_pos _).trans_le hmA
  have hU : 0 < U := by norm_num [U]
  have hsa : 0 < Real.sqrt w.a := Real.sqrt_pos.2 hw.a_pos
  have hlogm : Real.log m ≤ Real.log w.a + K * w.D := by
    have he := log_window_endpoint w hw.a_pos K
    exact (Real.log_le_log hm₀ hmB).trans_eq (by simpa only [mul_comm w.D] using he)
  have hA : w.a / U ≤ (m : ℝ) := by
    apply le_trans _ hmA
    rw [Window.endpoint, mul_neg, mul_comm w.D K, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (window_exp_lower hw.width) hw.a_pos.le
  have hS : Real.sqrt w.a / U ≤ Real.sqrt (m : ℝ) := by
    apply (Real.le_sqrt (div_nonneg hsa.le hU.le) hm₀.le).2
    rw [div_pow, Real.sq_sqrt hw.a_pos.le]
    exact (div_le_div_of_nonneg_left hw.a_pos.le hU (by norm_num [U])).trans hA
  have hell : 0 ≤ Real.log w.a + K * w.D := by
    have hA₁ := (window_lower_support w K hw).trans hmA
    exact (Real.log_nonneg (by linarith only [hA₁])).trans hlogm
  calc
    _ ≤ (Real.log w.a + K * w.D) / Real.sqrt (m : ℝ) :=
      div_le_div_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log.trans hlogm)
        (Real.sqrt_nonneg _)
    _ ≤ (Real.log w.a + K * w.D) / (Real.sqrt w.a / U) :=
      div_le_div_of_nonneg_left hell (div_pos hsa hU) hS
    _ = _ := by rw [div_div_eq_mul_div]

/-- The Λ-weighted sum is at most the shoulder contributions and the prime-power error. -/
theorem gap_prime_powers (w : Window) (g : CosineTest) (hw : WindowBounds w g.K)
    (hweight : g.weightSum < 1) (hgap : ¬PrimeIn (w.endpoint (-1)) (w.endpoint 1)) :
    primePowerSum w g ≤ shoulderSum w g + primePowerError w g.K := by
  classical
  let ell := Real.log w.a + g.K * w.D
  let C := ell * U / Real.sqrt w.a
  let S := Finset.range (⌊w.endpoint g.K⌋₊ + 1)
  let onShoulder (m : ℕ) : Prop := m.Prime ∧ 1 < |w.scale m| ∧ |w.scale m| ≤ g.K
  let atEndpoint (m : ℕ) : Prop := (m : ℝ) = w.endpoint (-1) ∨ (m : ℝ) = w.endpoint 1
  let properPower (m : ℕ) : Prop := ¬m.Prime ∧ IsPrimePow m ∧
    w.endpoint (-g.K) ≤ (m : ℝ) ∧ (m : ℝ) ≤ w.endpoint g.K
  let ends := S.filter atEndpoint
  let powers := S.filter properPower
  let f (m : ℕ) := ArithmeticFunction.vonMangoldt m / Real.sqrt (m : ℝ) * g.G (w.scale m)
  let sw (m : ℕ) := Real.log m / Real.sqrt (m : ℝ) * g.positivePart (w.scale m)
  have hU : 0 ≤ U := by norm_num [U]
  have hell : 0 ≤ ell := by
    dsimp [ell]
    linarith only [hw.log_a, mul_nonneg g.K_pos.le hw.D_pos.le]
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hell hU) (Real.sqrt_nonneg _)
  have h₁ (m : ℕ) : 0 ≤ if onShoulder m then sw m else 0 := by
    split
    next hm =>
      have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm.1.one_lt.le
      exact mul_nonneg (div_nonneg (Real.log_nonneg hm₁) (Real.sqrt_nonneg _)) (le_max_right _ _)
    next => exact le_rfl
  have h₂ (m : ℕ) : 0 ≤ if atEndpoint m then C else 0 := by split <;> positivity
  have h₃ (m : ℕ) : 0 ≤ if properPower m then C else 0 := by split <;> positivity
  have hpoint (m : ℕ) : f m ≤ (if onShoulder m then sw m else 0) +
      (if atEndpoint m then C else 0) + (if properPower m then C else 0) := by
    by_cases hm : IsPrimePow m
    swap
    · have hzero := ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hm
      simp only [f, hzero, zero_div, zero_mul]
      exact add_nonneg (add_nonneg (h₁ m) (h₂ m)) (h₃ m)
    by_cases hsup : w.scale m ∈ Icc (-g.K) g.K
    swap
    · simp only [f, g.G_eq_zero hsup, mul_zero]
      exact add_nonneg (add_nonneg (h₁ m) (h₂ m)) (h₃ m)
    have hm₀ : (0 : ℝ) < m := by exact_mod_cast (zero_lt_one.trans hm.one_lt)
    have heq : w.endpoint (w.scale m) = (m : ℝ) := w.endpoint_scale hw.a_pos hw.D_pos hm₀
    have hmono := (w.endpoint_strictMono hw.a_pos hw.D_pos).monotone
    have hmA : w.endpoint (-g.K) ≤ (m : ℝ) := (hmono hsup.1).trans_eq heq
    have hmB : (m : ℝ) ≤ w.endpoint g.K := heq.symm.trans_le (hmono hsup.2)
    have hcmp : f m ≤ C := by
      have hcoeff := div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
        (Real.sqrt_nonneg (m : ℝ))
      calc
        _ ≤ ArithmeticFunction.vonMangoldt m / Real.sqrt (m : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans <|
            (g.abs_G_le_weightSum (w.scale m)).trans hweight.le) hcoeff
        _ ≤ C := by simpa only [mul_one] using mangoldt_weight_bound w g.K hw hmA hmB
    by_cases hp : m.Prime
    · by_cases hsh : 1 < |w.scale m|
      · have hon : onShoulder m := ⟨hp, hsh, abs_le.2 hsup⟩
        have hprime₁ : (1 : ℝ) ≤ m := by exact_mod_cast hp.one_lt.le
        have hsw : f m ≤ sw m := by
          dsimp [f, sw]
          rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) <|
            div_nonneg (Real.log_nonneg hprime₁) (Real.sqrt_nonneg _)
        rw [if_pos hon]
        exact hsw.trans ((le_add_of_nonneg_right (h₂ m)).trans (le_add_of_nonneg_right (h₃ m)))
      · have ha : ¬|w.scale m| < 1 := by
          intro hlt
          have hscale := abs_lt.1 hlt
          have hstrict := w.endpoint_strictMono hw.a_pos hw.D_pos
          exact hgap ⟨m, hp, (hstrict hscale.1).trans_eq heq, heq.symm.trans_lt (hstrict hscale.2)⟩
        have hscale : |w.scale m| = 1 := le_antisymm (le_of_not_gt hsh) (le_of_not_gt ha)
        have hend : atEndpoint m := by
          rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 hscale with hright | hleft
          · exact Or.inr (heq.symm.trans (congrArg w.endpoint hright))
          · exact Or.inl (heq.symm.trans (congrArg w.endpoint hleft))
        rw [if_pos hend]
        exact hcmp.trans ((le_add_of_nonneg_left (h₁ m)).trans (le_add_of_nonneg_right (h₃ m)))
    · have hproper : properPower m := ⟨hp, hm, hmA, hmB⟩
      rw [if_pos hproper]
      exact hcmp.trans (le_add_of_nonneg_left (add_nonneg (h₁ m) (h₂ m)))
  have hend_count : (ends.card : ℝ) ≤ 2 := by
    let points : Finset ℝ := {w.endpoint (-1), w.endpoint 1}
    have hs : ends.card ≤ points.card := Finset.card_le_card_of_injOn (fun m : ℕ ↦ (m : ℝ))
      (fun m hm ↦ by
        have hm' : m ∈ ends := hm
        have hc : atEndpoint m := (Finset.mem_filter.1 hm').2
        simpa only [points, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using hc)
      (fun _ _ _ _ h ↦ Nat.cast_injective h)
    have ht : points.card ≤ 2 := by
      dsimp [points]
      simpa only [Finset.card_singleton] using Finset.card_insert_le (w.endpoint (-1)) {w.endpoint 1}
    exact_mod_cast hs.trans ht
  have hproper_count : (powers.card : ℝ) ≤ (ell / Real.log 2) * (1 + g.K * w.P * U) :=
    proper_prime_power_count w g.K hw g.K_pos.le (fun _ hm ↦ (Finset.mem_filter.1 hm).2)
  have hsum : primePowerSum w g ≤ shoulderSum w g + (ends.card : ℝ) * C + (powers.card : ℝ) * C := by
    calc
      _ ≤ ∑ m ∈ S, ((if onShoulder m then sw m else 0) + (if atEndpoint m then C else 0) +
          (if properPower m then C else 0)) := Finset.sum_le_sum (fun m _ ↦ hpoint m)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter onShoulder sw,
          ← Finset.sum_filter atEndpoint (fun _ ↦ C), ← Finset.sum_filter properPower (fun _ ↦ C),
          Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        rfl
  calc
    _ ≤ shoulderSum w g + (ends.card : ℝ) * C + (powers.card : ℝ) * C := hsum
    _ ≤ shoulderSum w g + 2 * C + ((ell / Real.log 2) * (1 + g.K * w.P * U)) * C :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hend_count hC))
        (mul_le_mul_of_nonneg_right hproper_count hC)
    _ = _ := by unfold primePowerError; dsimp [C, ell]; ring

end Legendre
