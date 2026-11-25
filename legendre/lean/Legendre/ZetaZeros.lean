import Legendre.AnalyticData

namespace Legendre

open Complex Set Filter
open scoped Topology

private theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  rintro rfl
  simp at hz

private theorem ne_one_of_re_lt_one {z : ℂ} (hz : z.re < 1) : z ≠ 1 := by
  rintro rfl
  simp at hz

private theorem completedZeta_eq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero (ne_zero_of_re_pos hs), div_mul_cancel₀ _
    (Gammaℝ_ne_zero_of_re_pos hs)]

private theorem order_completedZeta_eq {s : ℂ} (hs : s.re ∈ Ioo 0 1) :
    analyticOrderAt completedRiemannZeta s = analyticOrderAt riemannZeta s := by
  have hζ : AnalyticAt ℂ riemannZeta s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [continuous_re.continuousAt (isOpen_Iio.mem_nhds hs.2)] with z hz
    exact differentiableAt_riemannZeta (ne_one_of_re_lt_one hz)
  have hΓ : AnalyticAt ℂ Gammaℝ s := by
    simpa only [Pi.inv_def, inv_inv] using
      (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs.1))
  have heq : completedRiemannZeta =ᶠ[𝓝 s] riemannZeta * Gammaℝ := by
    filter_upwards [continuous_re.continuousAt (isOpen_Ioi.mem_nhds hs.1)] with z hz
    exact completedZeta_eq_mul hz
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hζ hΓ,
    hΓ.analyticOrderAt_eq_zero.mpr (Gammaℝ_ne_zero_of_re_pos hs.1), add_zero]

/-- The functional equation sends a critical-strip zero to the zero `1 − ρ`. -/
theorem reflect_nontrivialZero {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) :
    1 - ρ ∈ nontrivialZeros := by
  have hstrip : (1 - ρ).re ∈ Ioo 0 1 := by
    rw [sub_re, one_re]
    exact ⟨sub_pos.mpr hρ.2.1, sub_lt_self _ hρ.1⟩
  have hcompleted : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub, completedZeta_eq_mul hρ.1, hρ.2.2, zero_mul]
  rw [completedZeta_eq_mul hstrip.1, mul_eq_zero] at hcompleted
  exact ⟨hstrip.1, hstrip.2, hcompleted.resolve_right (Gammaℝ_ne_zero_of_re_pos hstrip.1)⟩

/-- Reflection of zeros preserves multiplicity. -/
theorem zeroMultiplicity_reflect {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) :
    zeroMultiplicity (1 - ρ) = zeroMultiplicity ρ := by
  have hρ' := reflect_nontrivialZero hρ
  have hlinear : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) ρ := by fun_prop
  have hderiv : deriv (fun z : ℂ ↦ 1 - z) ρ ≠ 0 := by
    simpa only [id_eq] using (show deriv (fun z : ℂ ↦ 1 - id z) ρ ≠ 0 by
      rw [((hasDerivAt_id ρ).const_sub (1 : ℂ)).deriv]
      simp)
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta) hlinear hderiv
  rw [show completedRiemannZeta ∘ (fun z : ℂ ↦ 1 - z) = completedRiemannZeta from
    funext completedRiemannZeta_one_sub] at h
  change analyticOrderAt completedRiemannZeta ρ = analyticOrderAt completedRiemannZeta (1 - ρ) at h
  rw [order_completedZeta_eq ⟨hρ.1, hρ.2.1⟩, order_completedZeta_eq ⟨hρ'.1, hρ'.2.1⟩] at h
  exact congrArg ENat.toNat h.symm

/-- Reflection is an involution on the set of nontrivial zeros. -/
def reflectZero : nontrivialZeros ≃ nontrivialZeros where
  toFun ρ := ⟨1 - ρ, reflect_nontrivialZero ρ.property⟩
  invFun ρ := ⟨1 - ρ, reflect_nontrivialZero ρ.property⟩
  left_inv _ := Subtype.ext (sub_sub_cancel _ _)
  right_inv _ := Subtype.ext (sub_sub_cancel _ _)

/-- The real part of a nontrivial zero under the Riemann hypothesis. -/
theorem nontrivialZero_re_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) :
    ρ.re = 1 / 2 := by
  refine hRH ρ hρ.2.2 ?_ (ne_one_of_re_lt_one hρ.2.1)
  rintro ⟨n, hn⟩
  have hp := hρ.1
  rw [hn] at hp
  norm_num [Complex.mul_re, Complex.add_re] at hp
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

end Legendre
