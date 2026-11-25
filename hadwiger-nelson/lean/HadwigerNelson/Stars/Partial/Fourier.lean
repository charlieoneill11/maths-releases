import HadwigerNelson.Stars.RealFourier

/-! The partial wave uses a common periodic lower step function on a whole
source rectangle. Its mean and Fourier magnitude give a gain bound because
the sum of the lower responses is pointwise dominated by the locked-star gain. -/

namespace HadwigerNelson.Stars
noncomputable section
open MeasureTheory

theorem lower_response_star_bound {d : ℕ} (hd : 0 < d) (W : Wave.Datum) (φ : Fin d → ℝ)
    (z : Plane) (a b : Wave.Label) (ha : Wave.colour W z = some a)
    (g : ℝ → ℝ) (period : Function.Periodic g (2*Real.pi)) (meas : Measurable g)
    {C : ℝ} (bound : ∀ θ, ‖g θ‖ ≤ C) (lower : ∀ θ, g θ ≤ signedResponse W z a b θ)
    (k : ℕ) (μ h : ℝ) (hμ : μ ≤ angleMean g) (hh : h ≤ ‖angleMoment k g‖) :
    d/2 * max 0 (μ + h * (‖∑ j, anglePhase (φ j)^k‖ / d)) ≤ angularGain W φ z := by
  let A := angleScore W φ z
  have Ai : Integrable A angleLaw := integrable_angleScore W φ measurable_id measurable_const
  have pointwise (θ : ℝ) : max 0 (∑ j, g (θ+φ j)) ≤ A θ := by
    apply (max_le_max_left 0 (Finset.sum_le_sum (fun j _ => lower (θ+φ j)))).trans
    simp only [A,angleScore,ha]
    exact localGain_ge_signed _ a b
  have H := fourier_lower φ g A k period meas bound Ai pointwise
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  have form : (d:ℝ)/2 * max 0 (μ + h * (‖∑ j, anglePhase (φ j)^k‖ / d)) =
      max 0 ((d:ℝ)*μ + ‖∑ j, anglePhase (φ j)^k‖*h)/2 := by
    rw [show (d:ℝ)/2 = (d:ℝ)*2⁻¹ by ring,mul_right_comm,←div_eq_mul_inv,
      mul_max_of_nonneg _ _ dp.le,mul_zero]
    congr 2
    field_simp
  rw [form]
  exact (div_le_div_of_nonneg_right (max_le_max_left 0 (add_le_add
    (mul_le_mul_of_nonneg_left hμ dp.le) (mul_le_mul_of_nonneg_left hh (norm_nonneg _))))
    (by norm_num)).trans H

end
end HadwigerNelson.Stars
