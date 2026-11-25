import HadwigerNelson.Stars.Gain
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith

/-! Expectation in the one-bad-edge inequality, and its complete-wave specialization. -/

open MeasureTheory
open scoped BigOperators

namespace HadwigerNelson.Stars

variable {Ω V : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Taking expectations gives equation (3) with a forest component term Y. -/
theorem one_bad_edge_expectation (S : Finset V) (E : Finset (V × V))
    (κ : Ω → V → Option (Fin 6)) (Y : Ω → ℕ)
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (component : ∀ᵐ ω ∂μ, (∃ v ∈ S, κ ω v = none) → 1 ≤ Y ω)
    (impossible : ¬ ∃ c : V → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2)
    (Yi : Integrable (fun ω => (Y ω : ℝ)) μ)
    (Xi : Integrable (fun ω => (badCount E (κ ω) : ℝ)) μ)
    (gi : ∀ v ∈ S, Integrable (fun ω => gain E (κ ω) v) μ) :
    1 ≤ (∫ ω, (Y ω : ℝ) ∂μ) + (∫ ω, (badCount E (κ ω) : ℝ) ∂μ) -
        (∑ v ∈ S, ∫ ω, gain E (κ ω) v ∂μ) / 4 := by
  have hpt : ∀ᵐ ω ∂μ, 1 ≤ (Y ω : ℝ) + badCount E (κ ω) - (∑ v ∈ S, gain E (κ ω) v) / 4 := by
    filter_upwards [component] with ω hω
    exact one_bad_edge_gain S E _ _ ends loops hω impossible
  have sgi := integrable_finset_sum S gi
  have h := integral_mono_ae (integrable_const (1 : ℝ)) ((Yi.add Xi).sub (sgi.div_const 4)) hpt
  have step : (1 : ℝ) ≤ ∫ ω, (Y ω : ℝ)+badCount E (κ ω)-
      (∑ v ∈ S, gain E (κ ω) v)/4 ∂μ := by
    simpa only [integral_const,probReal_univ,one_smul,Pi.add_apply,Pi.sub_apply] using h
  have split : (∫ ω, (Y ω : ℝ)+badCount E (κ ω)-(∑ v ∈ S, gain E (κ ω) v)/4 ∂μ) =
      (∫ ω, (Y ω : ℝ)+badCount E (κ ω) ∂μ) - (∫ ω, (∑ v ∈ S, gain E (κ ω) v)/4 ∂μ) :=
    integral_sub (Yi.add Xi) (sgi.div_const 4)
  have add : (∫ ω, (Y ω : ℝ)+badCount E (κ ω) ∂μ) =
      (∫ ω, (Y ω : ℝ) ∂μ)+(∫ ω, (badCount E (κ ω) : ℝ) ∂μ) := integral_add Yi Xi
  rw [split,add,integral_div,integral_finset_sum S gi] at step
  exact step

/-- Indicator for a bad edge at one placement. -/
noncomputable def badIndicator (κ : V → Option (Fin 6)) (e : V × V) : ℝ := by
  classical exact if Bad κ e then 1 else 0

theorem sum_badIndicator (E : Finset (V × V)) (κ : V → Option (Fin 6)) :
    (badCount E κ : ℝ) = ∑ e ∈ E, badIndicator κ e := by
  classical
  exact Finset.natCast_card_filter _ _

/-- A degree-uniform gain β and a one-edge probability bound p suffice for a
proper colouring provided the improved bound for the edge count is below one. -/
theorem colourable_of_locked_gain (S : Finset V) (E : Finset (V × V)) (κ : Ω → V → Option (Fin 6))
    (p β : ℝ) (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (full : ∀ᵐ ω ∂μ, ∀ v ∈ S, (κ ω v).isSome = true)
    (ei : ∀ e ∈ E, Integrable (fun ω => badIndicator (κ ω) e) μ)
    (ep : ∀ e ∈ E, (∫ ω, badIndicator (κ ω) e ∂μ) ≤ p)
    (gi : ∀ v ∈ S, Integrable (fun ω => gain E (κ ω) v) μ)
    (gp : ∀ v ∈ S, β * degree E v ≤ ∫ ω, gain E (κ ω) v ∂μ)
    (small : (E.card : ℝ) * (p - β / 2) < 1) :
    ∃ c : V → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2 := by
  by_contra impossible
  have component : ∀ᵐ ω ∂μ, (∃ v ∈ S, κ ω v = none) → 1 ≤ (0 : ℕ) := by
    filter_upwards [full] with ω h
    rintro ⟨v,hv,hb⟩
    simpa [hb] using h v hv
  have Xi : Integrable (fun ω => (badCount E (κ ω) : ℝ)) μ := by
    simp_rw [sum_badIndicator]
    exact integrable_finset_sum E ei
  have xle : (∫ ω, (badCount E (κ ω) : ℝ) ∂μ) ≤ (E.card : ℝ) * p := by
    simp_rw [sum_badIndicator]
    rw [integral_finset_sum E ei]
    calc
      _ ≤ ∑ _e ∈ E, p := Finset.sum_le_sum ep
      _ = _ := by simp
  have hs : ∑ v ∈ S, (degree E v : ℝ) = 2 * (E.card : ℝ) := by
    exact_mod_cast sum_degree S E ends
  have gsum := Finset.sum_le_sum gp
  rw [← Finset.mul_sum, hs] at gsum
  have key := one_bad_edge_expectation S E κ (fun _ => 0) ends loops component impossible
    (by simpa using (integrable_const (μ := μ) (0 : ℝ))) Xi gi
  simp only [Nat.cast_zero, integral_zero, zero_add] at key
  nlinarith

end HadwigerNelson.Stars
