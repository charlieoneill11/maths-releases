import HadwigerNelson.Stars.Fourier
import HadwigerNelson.Stars.ScoreIntegrable
import HadwigerNelson.Stars.AngularGain
import HadwigerNelson.Stars.LocalDifference
import HadwigerNelson.Stars.RealFourier.Character
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Angular colour responses for a physical star. The coefficient uses the positive
exponential convention. Translating an incident direction multiplies that coefficient
by the conjugate phase, preserving the required power-sum magnitude. -/

namespace HadwigerNelson.Stars
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

theorem norm_anglePhase_signAngle {d : ℕ} (φ : Fin d → ℝ) (b h : Bool) (k : ℕ) :
    ‖∑ j, anglePhase (signAngle b h (φ j)) ^ k‖ = ‖∑ j, anglePhase (φ j) ^ k‖ := by
  by_cases eq : b = h
  · simp [signAngle,eq]
  · simp only [signAngle,if_neg eq,anglePhase_neg,← map_pow,← map_sum,Complex.norm_conj]

abbrev angleLaw := Placement.uniformInterval (2*Real.pi)

def angleMean (g : ℝ → ℝ) : ℝ := ∫ θ, g θ ∂angleLaw

def angleMoment (k : ℕ) (g : ℝ → ℝ) : ℂ :=
  ∫ θ, (g θ : ℂ) * anglePhase θ^k ∂angleLaw

/-- Mean and moments use the same normalization on a full positive turn. -/
theorem angleIntegral_eq_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ θ, f θ ∂angleLaw) = (2*Real.pi)⁻¹ • ∫ θ in 0..2*Real.pi, f θ := by
  have h : (0:ℝ) ≤ 2*Real.pi := by positivity
  rw [angleLaw, Placement.uniformInterval, integral_smul_measure, intervalIntegral.integral_of_le h]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal h]

theorem angleMean_eq_interval (g : ℝ → ℝ) :
    angleMean g = (2*Real.pi)⁻¹ * ∫ θ in 0..2*Real.pi, g θ :=
  Placement.integral_uniformInterval (by positivity) g

theorem angleMoment_eq_interval (k : ℕ) (g : ℝ → ℝ) :
    angleMoment k g = (2*Real.pi)⁻¹ • ∫ θ in 0..2*Real.pi, (g θ : ℂ)*anglePhase θ^k :=
  angleIntegral_eq_interval _

/-- The normalized full-period average is unchanged by translating its argument.
This works for both scalar responses and their complex Fourier coefficients. -/
private theorem average_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : Function.Periodic f (2*Real.pi)) (u : ℝ) :
    (∫ θ, f (θ+u) ∂angleLaw) = ∫ θ, f θ ∂angleLaw := by
  rw [angleIntegral_eq_interval, angleIntegral_eq_interval, intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add, add_comm (2*Real.pi) u] using hf.intervalIntegral_add_eq u 0

theorem angleMoment_translate (k : ℕ) (g : ℝ → ℝ)
    (hg : Function.Periodic g (2*Real.pi)) (u : ℝ) :
    angleMoment k (fun θ => g (θ+u)) = conj (anglePhase u^k) * angleMoment k g := by
  let f (θ : ℝ) := (g θ : ℂ) * anglePhase θ^k
  have hf : Function.Periodic f (2*Real.pi) := fun t => by
    simp only [f, hg t, anglePhase_period t]
  have prod (θ : ℝ) : (g (θ+u) : ℂ) * anglePhase θ^k = conj (anglePhase u^k) * f (θ+u) := by
    conv_lhs => rw [anglePhase_shift k u θ]
    dsimp only [f]
    ring
  unfold angleMoment
  simp_rw [prod]
  erw [integral_const_mul]
  congr 1
  exact average_translate f hf u

theorem angleMean_translate (g : ℝ → ℝ) (hg : Function.Periodic g (2*Real.pi)) (u : ℝ) :
    angleMean (fun θ => g (θ+u)) = angleMean g := average_translate g hg u

/-- The one-neighbour colour response at the physical centre z. -/
def colourResponse (W : Wave.Datum) (z : Plane) (a : Wave.Label) (θ : ℝ) : ℝ :=
  labelIndicator (Wave.colour W (z+direction θ)) a

def signedResponse (W : Wave.Datum) (z : Plane) (a b : Wave.Label) (θ : ℝ) : ℝ :=
  colourResponse W z a θ - colourResponse W z b θ

theorem colourResponse_period (W : Wave.Datum) (z : Plane) (a : Wave.Label) :
    Function.Periodic (colourResponse W z a) (2*Real.pi) := by
  intro θ
  simp only [colourResponse, direction, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem measurable_colourResponse (W : Wave.Datum) (z : Plane) (a : Wave.Label) :
    Measurable (colourResponse W z a) := by
  have dir : Continuous direction := Placement.continuous_point Real.continuous_cos Real.continuous_sin
  have h : MeasurableSet {θ | Wave.colour W (z+direction θ) = some a} :=
    ((Wave.colour_fibre_open W a).preimage (continuous_const.add dir)).measurableSet
  exact Measurable.ite h measurable_const measurable_const

theorem norm_colourResponse_le (W : Wave.Datum) (z : Plane) (a : Wave.Label) (θ : ℝ) :
    ‖colourResponse W z a θ‖ ≤ 1 := by
  unfold colourResponse labelIndicator
  split <;> norm_num

theorem intervalIntegrable_colourResponse (W : Wave.Datum) (z : Plane) (a : Wave.Label) (l r : ℝ) :
    IntervalIntegrable (colourResponse W z a) volume l r := by
  apply intervalIntegrable_iff.mpr
  exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (measurable_colourResponse W z a).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_colourResponse_le W z a))

theorem intervalIntegrable_signedResponse (W : Wave.Datum) (z : Plane)
    (a b : Wave.Label) (l r : ℝ) : IntervalIntegrable (signedResponse W z a b) volume l r :=
  (intervalIntegrable_colourResponse W z a l r).sub (intervalIntegrable_colourResponse W z b l r)

private theorem translated_integrable {g : ℝ → ℝ} (meas : Measurable g) {C : ℝ}
    (bound : ∀ θ, ‖g θ‖ ≤ C) (φ : ℝ) :
    Integrable (fun θ => g (θ+φ)) angleLaw :=
  Integrable.of_bound (meas.comp (measurable_id.add measurable_const)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun θ => bound (θ+φ))

private theorem moment_term_integrable {g : ℝ → ℝ} (meas : Measurable g) {C : ℝ}
    (bound : ∀ θ, ‖g θ‖ ≤ C) (φ : ℝ) (k : ℕ) :
    Integrable (fun θ => (g (θ+φ) : ℂ) * anglePhase θ^k) angleLaw := by
  have gm : Measurable (fun θ : ℝ => (g (θ+φ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (meas.comp (measurable_id.add measurable_const))
  apply Integrable.of_bound (gm.mul (anglePhase_continuous.pow k).measurable).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun θ => by
    simpa only [norm_mul, Complex.norm_real, norm_pow, norm_anglePhase, one_pow, mul_one] using
      bound (θ+φ)

/-- A periodic real lower witness can be used in place of the exact signed response
whenever the positive part of its translated sum is dominated by the physical gain. -/
theorem fourier_lower {d : ℕ} (φ : Fin d → ℝ) (g A : ℝ → ℝ) (k : ℕ)
    (per : Function.Periodic g (2*Real.pi)) (meas : Measurable g) {C : ℝ}
    (bound : ∀ θ, ‖g θ‖ ≤ C) (Ai : Integrable A angleLaw)
    (hA : ∀ θ, max 0 (∑ j, g (θ+φ j)) ≤ A θ) :
    max 0 (d * angleMean g + ‖∑ j, anglePhase (φ j)^k‖ * ‖angleMoment k g‖) / 2 ≤
      angleMean A := by
  letI := Placement.uniformInterval_probability (show 0 < 2*Real.pi by positivity)
  let D (θ : ℝ) := ∑ j, g (θ+φ j)
  have each := translated_integrable meas bound
  have Di : Integrable D angleLaw := integrable_finset_sum _ (fun j _ => each (φ j))
  have mean : (∫ θ, D θ ∂angleLaw) = d * angleMean g := by
    unfold D
    rw [integral_finset_sum _ (fun j _ => each (φ j))]
    simp only [average_translate g per, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, angleMean]
  have coeff : angleMoment k D = (conj (∑ j, anglePhase (φ j)^k)) * angleMoment k g := by
    calc
      _ = ∑ j, angleMoment k (fun θ => g (θ+φ j)) := by
        unfold angleMoment
        simp_rw [D, Complex.ofReal_sum, Finset.sum_mul]
        exact integral_finset_sum _ (fun j _ => moment_term_integrable meas bound (φ j) k)
      _ = _ := by simp only [angleMoment_translate k g per, map_sum, Finset.sum_mul]
  have absle := fourier_norm_le (μ := angleLaw) D (fun θ => anglePhase θ^k)
    (fun θ => by rw [norm_pow, norm_anglePhase, one_pow])
  change ‖angleMoment k D‖ ≤ _ at absle
  rw [coeff, norm_mul, Complex.norm_conj] at absle
  have pt (θ : ℝ) : D θ + |D θ| ≤ 2*A θ := by
    have h : max 0 (D θ) ≤ A θ := hA θ
    rcases le_total 0 (D θ) with hθ | hθ
    · rw [max_eq_right hθ] at h
      rw [abs_of_nonneg hθ]
      linarith
    · rw [max_eq_left hθ] at h
      rw [abs_of_nonpos hθ]
      linarith
  have sumBound := integral_mono (Di.add Di.abs) (Ai.const_mul 2) pt
  change (∫ θ, D θ + |D θ| ∂angleLaw) ≤ (∫ θ, 2*A θ ∂angleLaw) at sumBound
  rw [integral_add Di Di.abs, integral_const_mul, mean] at sumBound
  have nn : 0 ≤ ∫ θ, A θ ∂angleLaw := integral_nonneg fun θ => (le_max_left ..).trans (hA θ)
  change max 0 _ / 2 ≤ ∫ θ, A θ ∂angleLaw
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), max_le_iff]
  constructor <;> linarith

/-- Lemma 21 for the signed response of a physical star, normalized by its degree. -/
theorem real_fourier_star_bound {d : ℕ} (hd : 0 < d) (W : Wave.Datum) (φ : Fin d → ℝ)
    (z : Plane) (a b : Wave.Label) (ha : Wave.colour W z = some a) (k : ℕ) (μ h : ℝ)
    (hμ : μ ≤ angleMean (signedResponse W z a b))
    (hh : h ≤ ‖angleMoment k (signedResponse W z a b)‖) :
    d/2 * max 0 (μ + h * (‖∑ j, anglePhase (φ j)^k‖ / d)) ≤ angularGain W φ z := by
  let g := signedResponse W z a b
  have per : Function.Periodic g (2*Real.pi) :=
    (colourResponse_period W z a).sub (colourResponse_period W z b)
  have meas : Measurable g := (measurable_colourResponse W z a).sub (measurable_colourResponse W z b)
  have bound (θ : ℝ) : ‖g θ‖ ≤ 2 := (norm_sub_le ..).trans
    (by linarith [norm_colourResponse_le W z a θ, norm_colourResponse_le W z b θ])
  have Ai : Integrable (angleScore W φ z) angleLaw := integrable_angleScore W φ measurable_id measurable_const
  have step (θ : ℝ) : max 0 (∑ j, g (θ+φ j)) ≤ angleScore W φ z θ := by
    simp only [angleScore,ha]
    exact localGain_ge_signed _ a b
  have H := fourier_lower φ g _ k per meas bound Ai step
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  have n : 0 ≤ ‖∑ j, anglePhase (φ j)^k‖ := norm_nonneg _
  change μ ≤ angleMean g at hμ
  change h ≤ ‖angleMoment k g‖ at hh
  calc
    _ = max 0 ((d:ℝ)*μ + ‖∑ j, anglePhase (φ j)^k‖*h)/2 := by
      rw [show (d:ℝ)/2 = (d:ℝ)*2⁻¹ by ring]
      rw [mul_right_comm, ← div_eq_mul_inv, mul_max_of_nonneg _ _ dp.le, mul_zero]
      congr 2
      field_simp
    _ ≤ _ := (div_le_div_of_nonneg_right (max_le_max_left 0 (add_le_add
      (mul_le_mul_of_nonneg_left hμ dp.le) (mul_le_mul_of_nonneg_left hh n))) (by norm_num)).trans H

/-- Lemma 21's native-colour comparison under the same physical rotation law. -/
theorem real_native_star_bound {d : ℕ} (hd : 0 < d) (W : Wave.Datum) (φ : Fin d → ℝ)
    (z : Plane) (a : Wave.Label) (ha : Wave.colour W z = some a) (f : ℝ)
    (hf : f ≤ angleMean (colourResponse W z a)) :
    d * max 0 (f - 1 / (d:ℝ)) ≤ angularGain W φ z := by
  letI := Placement.uniformInterval_probability (show 0 < 2*Real.pi by positivity)
  let g := colourResponse W z a
  let A := angleScore W φ z
  have each := translated_integrable (measurable_colourResponse W z a) (norm_colourResponse_le W z a)
  have Di : Integrable (fun θ => ∑ j, g (θ+φ j)) angleLaw :=
    integrable_finset_sum _ (fun j _ => each (φ j))
  have Ai : Integrable A angleLaw := integrable_angleScore W φ measurable_id measurable_const
  have pt (θ : ℝ) : (∑ j, g (θ+φ j)) - 1 ≤ A θ := by
    simp only [A, angleScore, ha]
    exact localGain_ge_native _ a
  have lower := integral_mono (Di.sub (integrable_const 1)) Ai pt
  change (∫ θ, (∑ j, g (θ+φ j)) - 1 ∂angleLaw) ≤ (∫ θ, A θ ∂angleLaw) at lower
  rw [integral_sub Di (integrable_const 1), integral_finset_sum _ (fun j _ => each (φ j))] at lower
  simp only [average_translate (colourResponse W z a) (colourResponse_period W z a), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, integral_const, probReal_univ, one_smul] at lower
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  rw [mul_max_of_nonneg _ _ dp.le, mul_zero, mul_sub, mul_one_div_cancel dp.ne']
  apply max_le (integral_nonneg (fun θ => (localGain_range _ _).1))
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hf dp.le) 1).trans lower

end
end HadwigerNelson.Stars
