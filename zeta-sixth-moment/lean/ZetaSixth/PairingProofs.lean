import ZetaSixth.MomentBasics
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Topology.ContinuousMap.Algebra

namespace ZetaSixth

open Filter Function MeasureTheory
open scoped Topology

private noncomputable def targetTest : Test :=
  fun _ => ⟨fun t => zetaLine t ^ 3, continuous_zetaLine.pow _⟩

private theorem numerator_eq_gram (Φ : Weight) (B : Test) (T : ℝ) :
    numerator Φ B T = gram Φ targetTest B T := rfl

private theorem gram_integrable (Φ : Weight) (B B' : Test) (T : ℝ) :
    Integrable (fun t => (Φ (t / T) : ℂ) * B T t * star (B' T t)) := by
  have hΦ : Continuous (fun t => (Φ (t / T) : ℂ)) :=
    Complex.continuous_ofReal.comp (Φ.continuous_rescale T)
  have hs : HasCompactSupport (fun t => (Φ (t / T) : ℂ)) :=
    (Φ.compactSupport_rescale T).comp_left Complex.ofReal_zero
  exact ((hΦ.mul (B T).continuous).mul
    (continuous_star.comp (B' T).continuous)).integrable_of_hasCompactSupport hs.mul_right.mul_right

private theorem gram_add_left (Φ : Weight) (B₁ B₂ D : Test) (T : ℝ) :
    gram Φ (B₁ + B₂) D T = gram Φ B₁ D T + gram Φ B₂ D T := by
  simp only [gram, Pi.add_apply, ContinuousMap.add_apply, mul_add, add_mul]
  exact integral_add (gram_integrable Φ B₁ D T) (gram_integrable Φ B₂ D T)

private theorem gram_add_right (Φ : Weight) (B D₁ D₂ : Test) (T : ℝ) :
    gram Φ B (D₁ + D₂) T = gram Φ B D₁ T + gram Φ B D₂ T := by
  simp only [gram, Pi.add_apply, ContinuousMap.add_apply, star_add, mul_add]
  exact integral_add (gram_integrable Φ B D₁ T) (gram_integrable Φ B D₂ T)

private theorem gram_smul_left (Φ : Weight) (r : ℝ) (B D : Test) (T : ℝ) :
    gram Φ (r • B) D T = r • gram Φ B D T := by
  simp only [gram, Pi.smul_apply, ContinuousMap.smul_apply,
    mul_smul_comm, smul_mul_assoc]
  exact integral_smul r (fun t => (Φ (t / T) : ℂ) * B T t * star (D T t))

private theorem gram_smul_right (Φ : Weight) (r : ℝ) (B D : Test) (T : ℝ) :
    gram Φ B (r • D) T = r • gram Φ B D T := by
  simp only [gram, Pi.smul_apply, ContinuousMap.smul_apply, star_smul, star_trivial,
    mul_smul_comm]
  exact integral_smul r (fun t => (Φ (t / T) : ℂ) * B T t * star (D T t))

private noncomputable def normalizedGram (Φ : Weight) (B D : Test) (T : ℝ) : ℝ :=
  (gram Φ B D T).re / timeNorm Φ T

private theorem normalizedGram_smul_left (Φ : Weight) (r : ℝ) (B D : Test) (T : ℝ) :
    normalizedGram Φ (r • B) D T = r * normalizedGram Φ B D T := by
  unfold normalizedGram
  rw [gram_smul_left, Complex.smul_re, smul_eq_mul, mul_div_assoc]

private theorem normalizedGram_smul_right (Φ : Weight) (r : ℝ) (B D : Test) (T : ℝ) :
    normalizedGram Φ B (r • D) T = r * normalizedGram Φ B D T := by
  unfold normalizedGram
  rw [gram_smul_right, Complex.smul_re, smul_eq_mul, mul_div_assoc]

set_option maxHeartbeats 1000000 in
private theorem gram_tendsto_in_span {𝒯 : Family} (h𝒯 : Faithful 𝒯) (Φ : Weight)
    {P Q : Test × Profile} (hP : P ∈ Submodule.span ℝ 𝒯) (hQ : Q ∈ Submodule.span ℝ 𝒯) :
    Tendsto (fun T => normalizedGram Φ P.1 Q.1 T) atTop (𝓝 (inner ℝ P.2 Q.2)) := by
  refine Submodule.span_induction₂ (s := 𝒯) (t := 𝒯) (p := fun P Q _ _ =>
    Tendsto (fun T => normalizedGram Φ P.1 Q.1 T) atTop (𝓝 (inner ℝ P.2 Q.2)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hP hQ
  · intro P Q hP hQ
    have h := (Complex.continuous_re.tendsto _).comp (h𝒯.2 Φ P.1 Q.1 P.2 Q.2 hP hQ)
    simpa [normalizedGram, Function.comp_def] using h
  · intro Q _
    simp [normalizedGram, gram]
  · intro P _
    simp [normalizedGram, gram]
  · intro P Q R _ _ _ hPR hQR
    simpa [normalizedGram, gram_add_left, add_div, inner_add_left] using hPR.add hQR
  · intro P Q R _ _ _ hPQ hPR
    simpa [normalizedGram, gram_add_right, add_div, inner_add_right] using hPQ.add hPR
  · intro r P Q _ _ h
    change Tendsto (fun T => normalizedGram Φ (r • P.1) Q.1 T) atTop
      (𝓝 (inner ℝ (r • P.2) Q.2))
    rw [real_inner_smul_left]
    exact (h.const_mul r).congr fun T => (normalizedGram_smul_left Φ r P.1 Q.1 T).symm
  · intro r P Q _ _ h
    change Tendsto (fun T => normalizedGram Φ P.1 (r • Q.1) T) atTop
      (𝓝 (inner ℝ P.2 (r • Q.2)))
    rw [real_inner_smul_right]
    exact (h.const_mul r).congr fun T => (normalizedGram_smul_right Φ r P.1 Q.1 T).symm

theorem scalar_inner (x y : ℝ) : inner ℝ x y = x * y := by
  calc
    inner ℝ x y = inner ℝ (x • (1 : ℝ)) (y • (1 : ℝ)) := by simp [smul_eq_mul]
    _ = x * y := by
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
        norm_one, one_pow, mul_one]

private theorem target_inner_eq (V P : Profile) (hV : (V : Point → ℝ) =ᵐ[chamberVolume] v) :
    (∫ x, v x * P x ∂chamberVolume) = inner ℝ V P := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hV] with x hx
  simp only [scalar_inner, hx]

private theorem numerator_tendsto_in_span {𝒯 : Family} (h𝒯 : Faithful 𝒯) (Φ : Weight)
    (V : Profile) (hV : (V : Point → ℝ) =ᵐ[chamberVolume] v)
    {P : Test × Profile} (hP : P ∈ Submodule.span ℝ 𝒯) :
    Tendsto (fun T => normalizedGram Φ targetTest P.1 T) atTop (𝓝 (inner ℝ V P.2)) := by
  refine Submodule.span_induction (p := fun P _ =>
    Tendsto (fun T => normalizedGram Φ targetTest P.1 T) atTop (𝓝 (inner ℝ V P.2))) ?_ ?_ ?_ ?_ hP
  · intro P hP
    have h := (Complex.continuous_re.tendsto _).comp (h𝒯.1 Φ P.1 P.2 hP)
    simpa [normalizedGram, Function.comp_def, ← numerator_eq_gram, target_inner_eq V P.2 hV] using h
  · simp [normalizedGram, gram]
  · intro P Q _ _ hP hQ
    simpa [normalizedGram, gram_add_right, add_div, inner_add_right] using hP.add hQ
  · intro r P _ hP
    change Tendsto (fun T => normalizedGram Φ targetTest (r • P.1) T) atTop
      (𝓝 (inner ℝ V (r • P.2)))
    rw [real_inner_smul_right]
    exact (hP.const_mul r).congr fun T => (normalizedGram_smul_right Φ r targetTest P.1 T).symm

private theorem quadratic_le_normSq (u b : ℂ) :
    2 * (u * star b).re - (b * star b).re ≤ Complex.normSq u := by
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  nlinarith [sq_nonneg (u.re - b.re), sq_nonneg (u.im - b.im)]

private theorem weighted_re (w : ℝ) (a b : ℂ) :
    ((w : ℂ) * a * b).re = w * (a * b).re := by
  rw [mul_assoc, Complex.re_ofReal_mul]

private theorem gram_quadratic_le_moment (Φ : Weight) (B : Test) (T : ℝ) :
    2 * (gram Φ targetTest B T).re - (gram Φ B B T).re ≤ smoothedMoment Φ T := by
  let num := fun t => (Φ (t / T) : ℂ) * (zetaLine t ^ 3) * star (B T t)
  let diag := fun t => (Φ (t / T) : ℂ) * (B T t) * star (B T t)
  have hN : Integrable num := gram_integrable Φ targetTest B T
  have hG : Integrable diag := gram_integrable Φ B B T
  have hcompare : ∀ t, 2 * (num t).re - (diag t).re ≤ Φ (t / T) * momentDensity t := by
    intro t
    have hm : Complex.normSq (zetaLine t ^ 3) = momentDensity t := by
      rw [momentDensity, Complex.normSq_eq_norm_sq, norm_pow]
      ring
    rw [show (num t).re = _ from weighted_re (Φ (t / T)) (zetaLine t ^ 3) (star (B T t)),
      show (diag t).re = _ from weighted_re (Φ (t / T)) (B T t) (star (B T t)), ← hm]
    calc
      _ = Φ (t / T) * (2 * (zetaLine t ^ 3 * star (B T t)).re -
          (B T t * star (B T t)).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (quadratic_le_normSq _ _) (Φ.nonnegative _)
  have h := integral_mono ((hN.re.const_mul 2).sub hG.re) (smoothIntegrable Φ T) hcompare
  rw [integral_sub' (hN.re.const_mul 2) hG.re, integral_const_mul,
    integral_re hN, integral_re hG] at h
  exact h

/- The quadratic objective yields the lower bound without a division by the Gram entry.
Its maximum over the profile span is attained by the orthogonal projection. -/
theorem bound_of_profile_score {𝒯 : Family} (h𝒯 : Faithful 𝒯)
    (V : Profile) (hV : (V : Point → ℝ) =ᵐ[chamberVolume] v)
    {P : Test × Profile} (hP : P ∈ Submodule.span ℝ 𝒯)
    {d : ℝ} (hd : d < (Nat.factorial 9 : ℝ) * (2 * inner ℝ V P.2 - ‖P.2‖ ^ 2)) :
    ∀ (Φ : Weight), ∀ᶠ T in atTop,
      d * momentScale T * (∫ t, Φ t) ≤ smoothedMoment Φ T := by
  intro Φ
  let score := fun T => 2 * normalizedGram Φ targetTest P.1 T - normalizedGram Φ P.1 P.1 T
  have hscore : Tendsto score atTop (𝓝 (2 * inner ℝ V P.2 - ‖P.2‖ ^ 2)) := by
    simpa only [real_inner_self_eq_norm_sq] using
      ((numerator_tendsto_in_span h𝒯 Φ V hV hP).const_mul 2).sub
        (gram_tendsto_in_span h𝒯 Φ hP hP)
  have h₉ : 0 < (Nat.factorial 9 : ℝ) := by exact_mod_cast Nat.factorial_pos 9
  have hd' : d / (Nat.factorial 9 : ℝ) < 2 * inner ℝ V P.2 - ‖P.2‖ ^ 2 := by
    apply (div_lt_iff₀ h₉).2
    simpa only [mul_comm] using hd
  filter_upwards [hscore.eventually_const_lt hd', eventually_gt_atTop (1 : ℝ)]
    with T hTd hT
  have htime := timeNorm_pos Φ hT
  calc
    d * momentScale T * (∫ t, Φ t) = (d / (Nat.factorial 9 : ℝ)) * timeNorm Φ T := by
      rw [timeNorm_eq]
      field_simp [h₉.ne']
    _ ≤ score T * timeNorm Φ T := mul_le_mul_of_nonneg_right hTd.le htime.le
    _ = 2 * (gram Φ targetTest P.1 T).re - (gram Φ P.1 P.1 T).re := by
      dsimp [score, normalizedGram]
      field_simp [htime.ne']
    _ ≤ _ := gram_quadratic_le_moment Φ P.1 T

end ZetaSixth
