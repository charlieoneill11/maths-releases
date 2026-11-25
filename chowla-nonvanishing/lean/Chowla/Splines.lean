import Chowla.SplineData
import Chowla.Certificate
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace Chowla

/-- The right-continuous convention at degree zero. Either endpoint convention gives
the same integrals in §7.1. -/
noncomputable def truncatedPower (c : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  if c ≤ x then (x - c) ^ j / j.factorial else 0

open Set MeasureTheory

/-- Successive primitives with zero left-hand boundary value. -/
noncomputable def lowerPrimitive : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, h => h
  | n + 1, h => fun x => ∫ u in Iic x, lowerPrimitive n h u

private theorem truncatedPower_indicator (c : ℝ) (j : ℕ) :
    truncatedPower c j = (Ici c).indicator (fun u => (u - c) ^ j / j.factorial) := rfl

theorem truncatedPower_integrableOn (c : ℝ) (j : ℕ) (x : ℝ) :
    IntegrableOn (truncatedPower c j) (Iic x) := by
  rw [truncatedPower_indicator, IntegrableOn, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ici, Ici_inter_Iic]
  exact (by fun_prop : Continuous (fun u : ℝ => (u - c) ^ j / j.factorial)).integrableOn_Icc

/-- Lower integration raises the order of a normalized truncated power. -/
theorem integral_truncatedPower (c : ℝ) (j : ℕ) :
    lowerPrimitive 1 (truncatedPower c j) = truncatedPower c (j + 1) := by
  funext x
  change (∫ u in Iic x, truncatedPower c j u) = _
  rw [truncatedPower_indicator, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, Ici_inter_Iic]
  by_cases h : c ≤ x
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
      intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_right (fun y : ℝ => y ^ j) c,
      sub_self, integral_pow, zero_pow (Nat.succ_ne_zero j), sub_zero,
      truncatedPower, if_pos h]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, div_div]
  · rw [Icc_eq_empty h, setIntegral_empty, truncatedPower, if_neg h]

private theorem beta_nat (a : ℝ) (ha : 0 < a) (i j : ℕ) :
    (∫ t in (0 : ℝ)..a, t ^ i * (a - t) ^ j) =
      a ^ (i + j + 1) * ((i.factorial : ℝ) * (j.factorial : ℝ) / (i + j + 1).factorial) := by
  have hsum : ((i : ℂ) + 1) + ((j : ℂ) + 1) = ((i + j + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  have hi : 0 < ((i : ℂ) + 1).re := by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  have hj : 0 < ((j : ℂ) + 1).re := by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  have hb := Complex.Gamma_mul_Gamma_eq_betaIntegral hi hj
  rw [hsum, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at hb
  have hfact : ((i + j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hb' : Complex.betaIntegral ((i : ℂ) + 1) ((j : ℂ) + 1) =
      (i.factorial : ℂ) * (j.factorial : ℂ) / (i + j + 1).factorial :=
    (eq_div_iff hfact).2 <| by simpa only [mul_comm] using hb.symm
  have he := Complex.betaIntegral_scaled ((i : ℂ) + 1) ((j : ℂ) + 1) ha
  rw [hsum] at he
  simp only [add_sub_cancel_right, Complex.cpow_natCast, hb'] at he
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  exact he

open scoped Convolution

private theorem convolve_apply (f g : ℝ → ℝ) (x : ℝ) :
    convolve f g x = ∫ t : ℝ, f t * g (x - t) := by
  simp [convolve, convolution_def, smul_eq_mul]

private theorem truncatedPower_integrand (c d x : ℝ) (i j : ℕ) :
    (fun t => truncatedPower c i t * truncatedPower d j (x - t)) =
      (Icc c (x - d)).indicator (fun t =>
        (t - c) ^ i / i.factorial * (x - t - d) ^ j / j.factorial) := by
  funext t
  by_cases hc : c ≤ t <;> by_cases hd : d ≤ x - t
  · have h : t ∈ Icc c (x - d) := ⟨hc, by linarith⟩
    simp [truncatedPower, hc, hd, h, div_mul_eq_mul_div]
    ring
  · have h : t ∉ Icc c (x - d) := fun ht => hd (by linarith [ht.2])
    simp [truncatedPower, hc, hd, h]
  · have h : t ∉ Icc c (x - d) := fun ht => hc ht.1
    simp [truncatedPower, hc, hd, h]
  · have h : t ∉ Icc c (x - d) := fun ht => hc ht.1
    simp [truncatedPower, hc, hd, h]

private theorem truncatedPower_product_integrable (c d x : ℝ) (i j : ℕ) :
    Integrable (fun t => truncatedPower c i t * truncatedPower d j (x - t)) := by
  rw [truncatedPower_integrand, integrable_indicator_iff measurableSet_Icc]
  exact (by fun_prop : Continuous (fun t : ℝ =>
    (t - c) ^ i / i.factorial * (x - t - d) ^ j / j.factorial)).integrableOn_Icc

/-- Convolution is the normalized beta identity for each pair of basis functions. -/
theorem convolution_truncatedPower (c d : ℝ) (i j : ℕ) :
    convolve (truncatedPower c i) (truncatedPower d j) =
      truncatedPower (c + d) (i + j + 1) := by
  funext x
  rw [convolve_apply, truncatedPower_integrand, integral_indicator measurableSet_Icc]
  by_cases h : c + d < x
  · have hcd : c ≤ x - d := by linarith
    have ha : 0 < x - d - c := by linarith
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd,
      truncatedPower, if_pos h.le]
    have he : (fun t : ℝ => (t - c) ^ i / i.factorial * (x - t - d) ^ j / j.factorial) =
        (fun t : ℝ => ((t - c) ^ i * ((x - d - c) - (t - c)) ^ j) /
          ((i.factorial : ℝ) * (j.factorial : ℝ))) := by
      funext t
      rw [show x - t - d = (x - d - c) - (t - c) by ring]
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right
      (fun t : ℝ => t ^ i * ((x - d - c) - t) ^ j) c, sub_self, beta_nat _ ha]
    rw [show x - d - c = x - (c + d) by ring]
    have hi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    field_simp
  · by_cases heq : c = x - d
    · have heq' : x = c + d := by linarith
      rw [← heq, integral_Icc_eq_integral_Ioc, Ioc_self, setIntegral_empty,
        heq', truncatedPower, if_pos le_rfl, sub_self]
      simp
    · have hcd : ¬ c ≤ x - d := by
        intro hc
        have : x - d ≤ c := by linarith
        exact heq (le_antisymm hc this)
      rw [Icc_eq_empty hcd, setIntegral_empty, truncatedPower,
        if_neg (by linarith : ¬ c + d ≤ x)]

namespace Spline

/-- Interpret a spline as a real-valued function. -/
noncomputable def toReal (p : Spline) (x : ℝ) : ℝ :=
  (p.map fun t => (t.coefficient : ℝ) * truncatedPower t.knot t.degree x).sum

theorem eval_sound (p : Spline) (x : ℚ) : (p.eval x : ℝ) = p.toReal x := by
  induction p with
  | nil => simp [eval, toReal]
  | cons t ts ih =>
    simp only [eval, toReal, List.map_cons, List.sum_cons] at ih ⊢
    rw [Rat.cast_add, ih]
    unfold truncatedPower
    by_cases h : t.knot ≤ x
    · rw [if_pos h, if_pos (by exact_mod_cast h)]
      push_cast
      rfl
    · have h' : ¬(t.knot : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
      simp [h, h']

@[simp] theorem toReal_nil (x : ℝ) : toReal [] x = 0 := rfl

@[simp] theorem toReal_cons (t : SplineTerm) (p : Spline) (x : ℝ) :
    toReal (t :: p) x = (t.coefficient : ℝ) * truncatedPower t.knot t.degree x + p.toReal x :=
  rfl

@[simp] theorem toReal_append (p q : Spline) (x : ℝ) :
    toReal (p ++ q) x = p.toReal x + q.toReal x := by
  simp [toReal, List.map_append, List.sum_append]

@[simp] theorem toReal_scale (p : Spline) (c : ℚ) (x : ℝ) :
    (p.scale c).toReal x = (c : ℝ) * p.toReal x := by
  induction p with
  | nil => simp [scale]
  | cons t p ih =>
    simp only [scale, List.map_cons, toReal_cons, Rat.cast_mul] at ih ⊢
    rw [ih]
    ring

private theorem toReal_integrableOn (p : Spline) (x : ℝ) :
    IntegrableOn p.toReal (Iic x) := by
  induction p with
  | nil => simpa only [toReal_nil] using (integrable_zero ℝ ℝ _ :
      Integrable (0 : ℝ → ℝ) (volume.restrict (Iic x)))
  | cons t p ih =>
    change Integrable (fun u => toReal (t :: p) u) (volume.restrict (Iic x))
    simp only [toReal_cons]
    exact ((truncatedPower_integrableOn t.knot t.degree x).const_mul _).add ih

private theorem primitive_one_sound (p : Spline) :
    (p.primitive 1).toReal = lowerPrimitive 1 p.toReal := by
  funext x
  change (p.primitive 1).toReal x = ∫ u in Iic x, p.toReal u
  induction p with
  | nil => simp [primitive]
  | cons t p ih =>
    simp only [primitive, List.map_cons, toReal_cons] at ih ⊢
    rw [integral_add ((truncatedPower_integrableOn t.knot t.degree x).const_mul _)
      (toReal_integrableOn p x), integral_const_mul, ← ih]
    change _ + _ = (t.coefficient : ℝ) * lowerPrimitive 1 (truncatedPower t.knot t.degree) x + _
    rw [integral_truncatedPower]

/-- The exact primitive agrees with the iterated real lower primitive. -/
theorem primitive_sound (p : Spline) (n : ℕ) :
    (p.primitive n).toReal = lowerPrimitive n p.toReal := by
  induction n with
  | zero =>
    have hp : p.primitive 0 = p := by
      induction p with
      | nil => rfl
      | cons t ts ih =>
        cases t
        simp [primitive] at ih ⊢
    rw [hp]
    rfl
  | succ n ih =>
    have hp : p.primitive (n + 1) = (p.primitive n).primitive 1 := by
      simp [primitive, List.map_map, Function.comp_def, Nat.add_assoc]
    rw [hp, primitive_one_sound, ih]
    rfl

private theorem term_product_integrable (t u : SplineTerm) (x : ℝ) :
    Integrable (fun v => ((t.coefficient : ℝ) * truncatedPower t.knot t.degree v) *
        ((u.coefficient : ℝ) * truncatedPower u.knot u.degree (x - v))) := by
  have hm : (fun v => ((t.coefficient : ℝ) * truncatedPower t.knot t.degree v) *
        ((u.coefficient : ℝ) * truncatedPower u.knot u.degree (x - v))) =
      (fun v => ((t.coefficient : ℝ) * (u.coefficient : ℝ)) *
        (truncatedPower t.knot t.degree v * truncatedPower u.knot u.degree (x - v))) := by
    funext v
    ring
  rw [hm]
  exact (truncatedPower_product_integrable t.knot u.knot x t.degree u.degree).const_mul _

private theorem term_spline_integrable (t : SplineTerm) (q : Spline) (x : ℝ) :
    Integrable (fun v => ((t.coefficient : ℝ) * truncatedPower t.knot t.degree v) * q.toReal (x - v)) := by
  induction q with
  | nil => simp
  | cons u q ih =>
    simp only [toReal_cons, mul_add]
    exact (term_product_integrable t u x).add ih

private theorem spline_product_integrable (p q : Spline) (x : ℝ) :
    Integrable (fun v => p.toReal v * q.toReal (x - v)) := by
  induction p with
  | nil => simp
  | cons t p ih =>
    simp only [toReal_cons, add_mul]
    exact (term_spline_integrable t q x).add ih

private theorem convolution_one_sound (t : SplineTerm) (q : Spline) (x : ℝ) :
    toReal (q.map fun u =>
      ⟨t.knot + u.knot, t.degree + u.degree + 1, t.coefficient * u.coefficient⟩) x =
      ∫ v : ℝ, ((t.coefficient : ℝ) * truncatedPower t.knot t.degree v) * q.toReal (x - v) := by
  induction q with
  | nil => simp
  | cons u q ih =>
    simp only [List.map_cons, toReal_cons, mul_add]
    rw [integral_add (term_product_integrable t u x) (term_spline_integrable t q x), ← ih]
    congr 1
    have hm : (fun v => ((t.coefficient : ℝ) * truncatedPower t.knot t.degree v) *
          ((u.coefficient : ℝ) * truncatedPower u.knot u.degree (x - v))) =
        (fun v => ((t.coefficient : ℝ) * (u.coefficient : ℝ)) *
          (truncatedPower t.knot t.degree v * truncatedPower u.knot u.degree (x - v))) := by
      funext v
      ring
    rw [hm, integral_const_mul, ← convolve_apply, convolution_truncatedPower, Rat.cast_mul,
      Rat.cast_add]

/-- The real convolution of spline interpretations agrees with the executable convolution. -/
theorem convolution_sound (p q : Spline) : (p.convolution q).toReal = convolve p.toReal q.toReal := by
  funext x
  rw [convolve_apply]
  induction p with
  | nil => simp [convolution]
  | cons t p ih =>
    simp only [convolution, List.flatMap_cons, toReal_append, toReal_cons, add_mul] at ih ⊢
    rw [integral_add (term_spline_integrable t q x) (spline_product_integrable p q x),
      ← ih, convolution_one_sound]

end Spline
end Chowla
