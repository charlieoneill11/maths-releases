import Chowla.SplineProfiles
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Chowla

open MeasureTheory Set
open scoped BigOperators

private theorem legendre_zero (x : ℝ) : legendre 0 x = 1 := rfl
private theorem legendre_first (x : ℝ) : legendre 1 x = x := rfl

private theorem legendre_rec (n : ℕ) (x : ℝ) :
    legendre (n + 2) x =
      ((2 * (n : ℝ) + 3) * x * legendre (n + 1) x -
        ((n : ℝ) + 1) * legendre n x) / ((n : ℝ) + 2) := rfl

private theorem legendre_rec_fun (n : ℕ) :
    legendre (n + 2) = fun x =>
      ((2 * (n : ℝ) + 3) * x * legendre (n + 1) x -
        ((n : ℝ) + 1) * legendre n x) / ((n : ℝ) + 2) :=
  funext (legendre_rec n)

private theorem contDiff_legendre_consecutive (n : ℕ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (legendre n) ∧ ContDiff ℝ k (legendre (n + 1)) := by
  induction n with
  | zero =>
    exact ⟨contDiff_const, contDiff_id⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n.succ + 1 = n + 2 by omega, legendre_rec_fun]
    have h₁ := ih.1
    have h₂ := ih.2
    fun_prop

private theorem contDiff_legendre (n : ℕ) (k : WithTop ℕ∞) : ContDiff ℝ k (legendre n) :=
  (contDiff_legendre_consecutive n k).1

private theorem differentiable_legendre (n : ℕ) : Differentiable ℝ (legendre n) :=
  (contDiff_legendre n 1).differentiable one_ne_zero

private theorem differentiable_deriv_legendre (n : ℕ) : Differentiable ℝ (deriv (legendre n)) :=
  ((contDiff_legendre n (1 + 1)).deriv').differentiable one_ne_zero

private theorem legendre_one (n : ℕ) : legendre n 1 = 1 := by
  suffices h : legendre n 1 = 1 ∧ legendre (n + 1) 1 = 1 from h.1
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n.succ + 1 = n + 2 by omega, legendre_rec, ih.1, ih.2]
    have hp : ((n : ℝ) + 2) ≠ 0 := by positivity
    apply (div_eq_iff hp).2
    ring

private theorem legendre_eval_neg (n : ℕ) (x : ℝ) :
    legendre n (-x) = (-1 : ℝ) ^ n * legendre n x := by
  suffices h : legendre n (-x) = (-1 : ℝ) ^ n * legendre n x ∧
      legendre (n + 1) (-x) = (-1 : ℝ) ^ (n + 1) * legendre (n + 1) x from h.1
  induction n with
  | zero => simp [legendre_zero, legendre_first]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n.succ + 1 = n + 2 by omega, legendre_rec, legendre_rec, ih.1, ih.2,
      pow_succ (-1 : ℝ) (n + 1), pow_succ (-1 : ℝ) n]
    ring

private theorem legendre_deriv_rec (n : ℕ) (x : ℝ) :
    deriv (legendre (n + 2)) x =
      ((2 * (n : ℝ) + 3) * (legendre (n + 1) x + x * deriv (legendre (n + 1)) x) -
        ((n : ℝ) + 1) * deriv (legendre n) x) / ((n : ℝ) + 2) := by
  have hp := (differentiable_legendre n x).hasDerivAt
  have hq := (differentiable_legendre (n + 1) x).hasDerivAt
  have h := ((((hasDerivAt_id x).mul hq).const_mul (2 * (n : ℝ) + 3)).sub
    (hp.const_mul ((n : ℝ) + 1))).div_const ((n : ℝ) + 2)
  rw [legendre_rec_fun]
  convert h.deriv using 1 <;> simp [id, mul_assoc]

private theorem legendre_deriv_identities (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * deriv (legendre n) x =
        ((n : ℝ) + 1) * (x * legendre n x - legendre (n + 1) x) ∧
      (1 - x ^ 2) * deriv (legendre (n + 1)) x =
        ((n : ℝ) + 1) * (legendre n x - x * legendre (n + 1) x) := by
  induction n with
  | zero =>
    have hz : legendre 0 = fun _ => 1 := funext legendre_zero
    have h1 : legendre 1 = id := funext legendre_first
    rw [hz, h1]
    simp [pow_two]
  | succ n ih =>
    rcases ih with ⟨hp, hq⟩
    have hN : ((n : ℝ) + 2) ≠ 0 := by positivity
    constructor
    · rw [show n.succ + 1 = n + 2 by omega, legendre_rec, hq, Nat.cast_succ]
      field_simp
      ring
    · rw [show n.succ + 1 = n + 2 by omega, legendre_deriv_rec, legendre_rec, Nat.cast_succ]
      field_simp
      linear_combination (2 * (n : ℝ) + 3) * x * hq - ((n : ℝ) + 1) * hp

private noncomputable def legendreFlux (n : ℕ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * deriv (legendre n) x

private theorem legendreFlux_deriv (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (legendreFlux n) (-((n : ℝ) * ((n : ℝ) + 1)) * legendre n x) x := by
  have hEq : legendreFlux n = fun x =>
      ((n : ℝ) + 1) * (x * legendre n x - legendre (n + 1) x) :=
    funext fun x => (legendre_deriv_identities n x).1
  have hp := (differentiable_legendre n x).hasDerivAt
  have hq := (differentiable_legendre (n + 1) x).hasDerivAt
  have h := (((hasDerivAt_id x).mul hp).sub hq).const_mul ((n : ℝ) + 1)
  rw [hEq]
  convert h using 1
  simp only [id_eq, one_mul]
  have hpos : 0 < 1 - x ^ 2 := by
    have hmul := mul_pos (show 0 < 1 - x by linarith [hx.2])
      (show 0 < 1 + x by linarith [hx.1])
    nlinarith
  apply (mul_left_cancel₀ hpos.ne' : ∀ {b c : ℝ}, (1 - x ^ 2) * b = (1 - x ^ 2) * c → b = c)
  obtain ⟨hp', hq'⟩ := legendre_deriv_identities n x
  linear_combination ((n : ℝ) + 1) * hq' - ((n : ℝ) + 1) * x * hp'

private theorem hasDerivAt_one_sub_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).fun_pow 2) using 1
  simp [id]

private theorem legendre_ode (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) * deriv (deriv (legendre n)) x =
      2 * x * deriv (legendre n) x - (n : ℝ) * ((n : ℝ) + 1) * legendre n x := by
  have hd := (differentiable_deriv_legendre n x).hasDerivAt
  have hd' := ((hasDerivAt_one_sub_sq x).mul hd).deriv
  have hFlux := (legendreFlux_deriv n x hx).deriv
  change deriv (legendreFlux n) x =
    -2 * x * deriv (legendre n) x + (1 - x ^ 2) * deriv (deriv (legendre n)) x at hd'
  rw [hd'] at hFlux
  linear_combination hFlux

private noncomputable def legendreEnergy (n : ℕ) (x : ℝ) : ℝ :=
  (legendre n x) ^ 2 + (1 - x ^ 2) * (deriv (legendre n) x) ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))

private theorem legendreEnergy_deriv (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (legendreEnergy n)
      (2 * x * (deriv (legendre n) x) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) x := by
  have hp := (differentiable_legendre n x).hasDerivAt
  have hd := (differentiable_deriv_legendre n x).hasDerivAt
  have H := (hp.fun_pow 2).add
    (((hasDerivAt_one_sub_sq x).mul (hd.fun_pow 2)).div_const ((n : ℝ) * ((n : ℝ) + 1)))
  convert H using 1
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hN : (n : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
  have he := legendre_ode n x hx
  have he' : (1 - x ^ 2) * (2 * deriv (legendre n) x *
      deriv (deriv (legendre n)) x) =
      2 * deriv (legendre n) x *
        (2 * x * deriv (legendre n) x - (n : ℝ) * ((n : ℝ) + 1) * legendre n x) := by
    linear_combination 2 * deriv (legendre n) x * he
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [he']
  field_simp
  ring

/-- The standard bound for every Legendre polynomial on its normalizing interval. -/
theorem abs_legendre_le_one (n : ℕ) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |legendre n x| ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn, legendre_zero]
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hm : MonotoneOn (legendreEnergy n) (Icc (0 : ℝ) 1) := by
    have hp := differentiable_legendre n
    have hd := differentiable_deriv_legendre n
    have hdiff : Differentiable ℝ (legendreEnergy n) := by
      unfold legendreEnergy
      fun_prop
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(legendreEnergy_deriv n hn' t ⟨by linarith [ht.1], ht.2⟩).deriv]
    have := ht.1
    positivity
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |legendre n t| ≤ 1 := by
    have ht₂ := ht.2
    have ht₁ := ht.1
    have hsq : 0 ≤ 1 - t ^ 2 := by nlinarith [mul_nonneg ht₁ (sub_nonneg.mpr ht₂)]
    apply (sq_le_one_iff_abs_le_one _).1
    calc
      (legendre n t) ^ 2 ≤ legendreEnergy n t := by
        unfold legendreEnergy
        have h : 0 ≤ (1 - t ^ 2) * deriv (legendre n) t ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) := by positivity
        linarith
      _ ≤ legendreEnergy n 1 := hm ht (by simp) ht₂
      _ = 1 := by simp [legendreEnergy, legendre_one]
  by_cases hx0 : 0 ≤ x
  · exact hbound x ⟨hx0, hx.2⟩
  · have h := hbound (-x) ⟨by linarith, by linarith [hx.1]⟩
    rwa [legendre_eval_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h

private theorem integral_legendre_eq_zero (n : ℕ) (hn : 0 < n) :
    (∫ x in (-1 : ℝ)..1, legendre n x) = 0 := by
  have hcont : Continuous (legendreFlux n) := by
    have h := (differentiable_deriv_legendre n).continuous
    unfold legendreFlux
    fun_prop
  have hp := (differentiable_legendre n).continuous
  have hi : IntervalIntegrable (fun x => -((n : ℝ) * ((n : ℝ) + 1)) * legendre n x)
      volume (-1) 1 := ((continuous_const.mul hp).intervalIntegrable (-1) 1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (-1 : ℝ) ≤ 1)
    hcont.continuousOn (legendreFlux_deriv n) hi
  have hL : legendreFlux n (-1) = 0 := by norm_num [legendreFlux]
  have hR : legendreFlux n 1 = 0 := by norm_num [legendreFlux]
  rw [intervalIntegral.integral_const_mul, hL, hR, sub_zero] at h
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (mul_ne_zero hn'.ne' (by positivity)))

theorem legendreProfile_integral (s : ℝ) (hs : 0 < s) (c : List ℝ) :
    (∫ u : ℝ, legendreProfile s c u) = 0 := by
  rw [legendreProfile, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -s ≤ s)]
  have hi (j : Fin c.length) :
      IntervalIntegrable (fun u : ℝ => c.get j * legendre (2 * (j.val + 1)) (u / s)) volume (-s) s := by
    have hc := (differentiable_legendre (2 * (j.val + 1))).continuous
    exact (continuous_const.mul (hc.comp (continuous_id.div_const s))).intervalIntegrable (-s) s
  rw [intervalIntegral.integral_finset_sum fun j _ => hi j]
  apply Finset.sum_eq_zero
  intro j _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div _ hs.ne',
    neg_div, div_self hs.ne', integral_legendre_eq_zero _ (by omega), smul_zero, mul_zero]

theorem legendreProfile_bound (s : ℝ) (hs : 0 < s) (c : List ℝ) (u : ℝ) :
    |legendreProfile s c u| ≤ (c.map abs).sum := by
  unfold legendreProfile
  have hsum : (c.map abs).sum = ∑ i : Fin c.length, |c.get i| := by
    rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
    rfl
  rw [hsum]
  by_cases h : u ∈ Icc (-s) s
  · rw [indicator_of_mem h]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    have hmem : u / s ∈ Icc (-1 : ℝ) 1 := by
      exact ⟨(le_div_iff₀ hs).2 (by linarith [h.1]), (div_le_one hs).2 h.2⟩
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_legendre_le_one _ _ hmem)
  · rw [indicator_of_notMem h, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

end Chowla
