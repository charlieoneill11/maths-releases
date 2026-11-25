import Legendre.CosineTail
import Legendre.ExplicitFormula
import Legendre.GapElementary
import Legendre.ZeroSum

namespace Legendre

private theorem abs_weightedZeroTerm_le (w : Window) (g : CosineTest) (ρ : nontrivialZeros) :
    ‖weightedZeroTerm w g ρ‖ ≤ weightedZeroNorm g.F w.D ρ := by
  unfold weightedZeroTerm weightedZeroNorm Window.Δ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ zeroMultiplicity ρ)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- Proposition 17 for the empty correction set, assembled from the smoothed explicit formula. -/
theorem gap_condition_of_formula (hRH : RiemannHypothesis) (h : CitedFacts) (g : CosineTest)
    (hK : 1 ≤ g.K) (hwgt : g.weightSum < 1) (hmass : g.mass < 4)
    (w : Window) (hw : WindowBounds w g.K) (hgap : ¬ PrimeIn (w.endpoint (-1)) (w.endpoint 1))
    (hformula : primePowerSum w g + w.D * (∑' ρ : nontrivialZeros, weightedZeroTerm w g ρ) +
      w.D * (∑' k, trivialZeroTerm w g k) = poleTerm w g) :
    w.P * g.F 0 ≤ shoulderSum w g + fourierMass g.F * Real.log (1 / w.D) + logMoment g.F +
      primePowerError w g.K + 2 * w.D *
        ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * totalVariation g.F +
          0.15 * logVariation g.F + 4) + 1 / 10 ^ 12 := by
  have hD : w.D < 1 := by
    have hKmul := mul_le_mul_of_nonneg_right hK hw.D_pos.le
    have hwidth := hw.width
    norm_num [U] at hwidth
    linarith
  obtain ⟨hV₀, hV₁⟩ := g.derivative_integration_bounds
  obtain ⟨hsum, hnorm⟩ := zero_sum_bound hRH h g.F g.F_even g.F_contDiff_one g.F_decay
    hV₀ hV₁ g.mass g.abs_F_le_mass w.D hw.D_pos hD
  have hsigned := Summable.of_norm_bounded hsum (abs_weightedZeroTerm_le w g)
  have hweighted := hsigned.tsum_le_tsum
    (fun ρ ↦ (le_abs_self (weightedZeroTerm w g ρ)).trans (abs_weightedZeroTerm_le w g ρ)) hsum
  have hzeros := (mul_le_mul_of_nonneg_left hweighted hw.D_pos.le).trans hnorm
  have hM := mul_le_mul_of_nonneg_left hmass.le (show 0 ≤ 2 * w.D by positivity [hw.D_pos])
  have htrivial := (le_abs_self _).trans (gap_trivial_zeros w g hw hK hmass).2.le
  have hpole := gap_pole_lower w g hw hK hmass
  have hpow := gap_prime_powers w g hw hwgt hgap
  linarith only [hformula, hzeros, hM, htrivial, hpole, hpow]

/-- Proposition 17 for the correction set used in Proposition 22. -/
theorem gap_condition (hRH : RiemannHypothesis) (h : CitedFacts) (g : CosineTest)
    (hK₁ : 1 ≤ g.K) (_hK₂ : g.K ≤ 5 / 2) (hwgt : g.weightSum < 1) (hmass : g.mass < 4)
    (w : Window) (hw : WindowBounds w g.K) (hgap : ¬ PrimeIn (w.endpoint (-1)) (w.endpoint 1)) :
    w.P * g.F 0 ≤ shoulderSum w g + fourierMass g.F * Real.log (1 / w.D) + logMoment g.F +
      primePowerError w g.K + 2 * w.D *
        ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * totalVariation g.F +
          0.15 * logVariation g.F + 4) + 1 / 10 ^ 12 :=
  gap_condition_of_formula hRH h g hK₁ hwgt hmass w hw hgap
    (smoothed_explicit_formula hRH h g w hw.D_pos (window_lower_support w g.K hw)).2.2

end Legendre
