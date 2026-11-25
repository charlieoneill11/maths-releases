import Chowla.Certificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Chowla

open Filter MeasureTheory
open scoped BigOperators Topology

/-- The absolute Taylor coefficient at exponent `2 * n + parity`, evaluated at x. -/
noncomputable def trigTerm (parity : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + parity) / (2 * n + parity).factorial

/-- The first n terms of the cosine series (parity zero) or sine series (parity one). -/
noncomputable def trigTaylor (parity n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * trigTerm parity x k

private theorem trigTerm_antitone (parity : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (trigTerm parity x) := by
  intro m n hmn
  have hdeg : 2 * m + parity ≤ 2 * n + parity := by omega
  have hden : (0 : ℝ) < ((2 * m + parity).factorial : ℝ) := by positivity
  have hpow := pow_le_pow_of_le_one h0 h1 hdeg
  have hfac : ((2 * m + parity).factorial : ℝ) ≤ ((2 * n + parity).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hdeg
  exact (div_le_div_of_nonneg_left (by positivity) hden hfac).trans
    (div_le_div_of_nonneg_right hpow (le_of_lt hden))

private theorem trigTerm_summable (parity : ℕ) (x : ℝ) :
    Summable (trigTerm parity x) :=
  (Real.summable_pow_div_factorial x).comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n + parity) from fun _ _ eq => by dsimp at eq; omega)

private theorem hasSum_cos_terms (x : ℝ) :
    HasSum (fun k => (-1 : ℝ) ^ k * trigTerm 0 x k) (Real.cos x) := by
  simpa only [trigTerm, Nat.add_zero, mul_div_assoc] using Real.hasSum_cos x

private theorem hasSum_sin_terms (x : ℝ) :
    HasSum (fun k => (-1 : ℝ) ^ k * trigTerm 1 x k) (Real.sin x) := by
  simpa only [trigTerm, mul_div_assoc] using Real.hasSum_sin x

theorem cos_taylor_error {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    |Real.cos x - trigTaylor 0 n x| ≤ trigTerm 0 x n := by
  rw [← (hasSum_cos_terms x).tsum_eq]
  exact alternating_series_error_bound _ (trigTerm_antitone 0 h0 h1) (trigTerm_summable 0 x) n

theorem sin_taylor_error {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    |Real.sin x - trigTaylor 1 n x| ≤ trigTerm 1 x n := by
  rw [← (hasSum_sin_terms x).tsum_eq]
  exact alternating_series_error_bound _ (trigTerm_antitone 1 h0 h1) (trigTerm_summable 1 x) n

private theorem cos_quarter_bounds :
    trigTaylor 0 8 (1 / 4) ≤ Real.cos (1 / 4) ∧
      Real.cos (1 / 4) ≤ trigTaylor 0 7 (1 / 4) := by
  have ha := trigTerm_antitone 0 (x := 1 / 4) (by norm_num) (by norm_num)
  have ht := (hasSum_cos_terms (1 / 4)).tendsto_sum_nat
  exact ⟨ha.alternating_series_le_tendsto ht 4, ha.tendsto_le_alternating_series ht 3⟩

private theorem sin_quarter_bounds :
    trigTaylor 1 8 (1 / 4) ≤ Real.sin (1 / 4) ∧
      Real.sin (1 / 4) ≤ trigTaylor 1 7 (1 / 4) := by
  have ha := trigTerm_antitone 1 (x := 1 / 4) (by norm_num) (by norm_num)
  have ht := (hasSum_sin_terms (1 / 4)).tendsto_sum_nat
  exact ⟨ha.alternating_series_le_tendsto ht 4, ha.tendsto_le_alternating_series ht 3⟩

private theorem sin_quarter_pos : 0 < Real.sin (1 / 4) := by
  refine lt_of_lt_of_le ?_ sin_quarter_bounds.1
  norm_num [trigTaylor, trigTerm, Finset.sum_range_succ, Nat.factorial]

private theorem cot_quarter_lt_of_taylor {c : ℝ} (hc : 0 ≤ c)
    (h : trigTaylor 0 7 (1 / 4) < c * trigTaylor 1 8 (1 / 4)) :
    Real.cot (1 / 4) < c := by
  rw [Real.cot_eq_cos_div_sin, div_lt_iff₀ sin_quarter_pos]
  exact (cos_quarter_bounds.2.trans_lt h).trans_le
    (mul_le_mul_of_nonneg_left sin_quarter_bounds.1 hc)

private theorem lt_cot_quarter_of_taylor {c : ℝ} (hc : 0 ≤ c)
    (h : c * trigTaylor 1 7 (1 / 4) < trigTaylor 0 8 (1 / 4)) :
    c < Real.cot (1 / 4) := by
  rw [Real.cot_eq_cos_div_sin, lt_div_iff₀ sin_quarter_pos]
  exact ((mul_le_mul_of_nonneg_left sin_quarter_bounds.2 hc).trans_lt h).trans_le
    cos_quarter_bounds.1

/-- The rational upper enclosure of Lemma 31. -/
theorem cot_upper : Real.cot (1 / 4) < 3.916317365 := by
  apply cot_quarter_lt_of_taylor (by norm_num)
  norm_num [trigTaylor, trigTerm, Finset.sum_range_succ, Nat.factorial]

/-- The rational coefficient in the approximation in Lemma 29. -/
def HstarFactorQ : ℚ := 61453967058074 / 10^14

noncomputable def Hstar : ℝ → ℝ :=
  (Set.Icc (-1) 1).indicator fun u =>
    let x := |u| / 2
    (HstarFactorQ : ℝ) * trigTaylor 0 7 x + (1 / 4 - (HstarFactorQ : ℝ)) * trigTaylor 1 6 x

private theorem Hstar_factor_error :
    |(1 + Real.cot (1 / 4)) / 8 - (HstarFactorQ : ℝ)| < 5 / (10 : ℝ)^15 := by
  have hu : Real.cot (1 / 4) < 8 * ((HstarFactorQ : ℝ) + 5 / (10 : ℝ)^15) - 1 := by
    apply cot_quarter_lt_of_taylor (by norm_num [HstarFactorQ])
    norm_num [HstarFactorQ, trigTaylor, trigTerm, Finset.sum_range_succ, Nat.factorial]
  have hl : 8 * ((HstarFactorQ : ℝ) - 5 / (10 : ℝ)^15) - 1 < Real.cot (1 / 4) := by
    apply lt_cot_quarter_of_taylor (by norm_num [HstarFactorQ])
    norm_num [HstarFactorQ, trigTaylor, trigTerm, Finset.sum_range_succ, Nat.factorial]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem Hstar_error_inside {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    |H u - Hstar u| ≤ 1 / (10 : ℝ)^12 := by
  let x := |u| / 2
  let A := (1 + Real.cot (1 / 4)) / 8
  let B : ℝ := HstarFactorQ
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 / 2 := div_le_div_of_nonneg_right (abs_le.mpr hu) (by norm_num)
  have hx2 : x ≤ 1 := hx1.trans (by norm_num)
  have hcos := cos_taylor_error hx0 hx2 7
  have hsin := sin_taylor_error hx0 hx2 6
  have hcos' : |Real.cos x - trigTaylor 0 7 x| ≤ (1 / 2 : ℝ)^14 / ((14 : ℕ).factorial : ℝ) := by
    refine hcos.trans ?_
    change x ^ 14 / ((14 : ℕ).factorial : ℝ) ≤ (1 / 2 : ℝ)^14 / ((14 : ℕ).factorial : ℝ)
    gcongr
  have hsin' : |Real.sin x - trigTaylor 1 6 x| ≤ (1 / 2 : ℝ)^13 / ((13 : ℕ).factorial : ℝ) := by
    refine hsin.trans ?_
    change x ^ 13 / ((13 : ℕ).factorial : ℝ) ≤ (1 / 2 : ℝ)^13 / ((13 : ℕ).factorial : ℝ)
    gcongr
  have hB : |B| ≤ 1 := by norm_num [B, HstarFactorQ]
  have hB' : |1 / 4 - B| ≤ 1 := by norm_num [B, HstarFactorQ]
  have hAB : |A - B| ≤ 5 / (10 : ℝ)^15 := Hstar_factor_error.le
  have htrig : |Real.cos x - Real.sin x| ≤ 2 :=
    (abs_sub _ _).trans (by
      simpa only [one_add_one_eq_two] using add_le_add (Real.abs_cos_le_one x) (Real.abs_sin_le_one x))
  rw [H, Hstar, Set.indicator_of_mem hu, Set.indicator_of_mem hu]
  change |A * Real.cos x + (1 / 4 - A) * Real.sin x -
    (B * trigTaylor 0 7 x + (1 / 4 - B) * trigTaylor 1 6 x)| ≤ _
  have heq : A * Real.cos x + (1 / 4 - A) * Real.sin x -
      (B * trigTaylor 0 7 x + (1 / 4 - B) * trigTaylor 1 6 x) =
        (B * (Real.cos x - trigTaylor 0 7 x) + (1 / 4 - B) * (Real.sin x - trigTaylor 1 6 x)) +
        (A - B) * (Real.cos x - Real.sin x) := by ring
  rw [heq]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  simp only [abs_mul]
  calc
    _ ≤ 1 * ((1 / 2 : ℝ)^14 / ((14 : ℕ).factorial : ℝ)) +
        1 * ((1 / 2 : ℝ)^13 / ((13 : ℕ).factorial : ℝ)) + (5 / (10 : ℝ)^15) * 2 := by
      gcongr
    _ ≤ _ := by norm_num [Nat.factorial]

/-- The uniform pointwise enclosure of Lemma 29. -/
theorem Hstar_pointwise_error (u : ℝ) : |H u - Hstar u| ≤ 1 / (10 : ℝ)^12 := by
  by_cases hu : u ∈ Set.Icc (-1 : ℝ) 1
  · exact Hstar_error_inside hu
  · simp [H, Hstar, Set.indicator_of_notMem hu]

/-- The L¹ enclosure of Lemma 29. -/
theorem Hstar_integral_error :
    (∫ u : ℝ, |H u - Hstar u|) ≤ 2 / (10 : ℝ)^12 := by
  let I := Set.Icc (-1 : ℝ) 1
  let bound : ℝ := 1 / (10 : ℝ)^12
  have hI : MeasurableSet I := measurableSet_Icc
  have hI_integrable : Integrable (I.indicator fun _ => bound) :=
    (integrable_indicator_iff hI).2 (integrableOn_const (by exact isCompact_Icc.measure_lt_top.ne))
  calc
    _ ≤ ∫ u : ℝ, I.indicator (fun _ => bound) u := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hI_integrable
        (Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ I
      · simpa only [Set.indicator_of_mem hu] using Hstar_pointwise_error u
      · have hu' : u ∉ Set.Icc (-1 : ℝ) 1 := hu
        simp [H, Hstar, Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']
    _ = 2 / (10 : ℝ)^12 := by
      rw [integral_indicator hI, setIntegral_const, Real.volume_real_Icc]
      norm_num [I, bound]

end Chowla
