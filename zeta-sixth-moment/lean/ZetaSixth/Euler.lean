import ZetaSixth.Statement
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

namespace ZetaSixth

private theorem choose_eq_prod (n k : ℕ) :
    ((n + k).choose k : ℝ) =
      (∏ i ∈ Finset.range k, ((n : ℝ) + i + 1)) / (k.factorial : ℝ) := by
  have hf : (Nat.factorial (n + k) : ℝ) =
      (n.factorial : ℝ) * ∏ i ∈ Finset.range k, ((n : ℝ) + i + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show n + k.succ = n + k + 1 from rfl, Nat.factorial_succ, Nat.cast_mul, ih,
          Finset.prod_range_succ]
        push_cast
        ring
  have hchoose : ((n + k).choose k : ℝ) =
      ((n + k).factorial : ℝ) / ((k.factorial : ℝ) * n.factorial) := by
    simpa only [Nat.add_comm k n] using (Nat.cast_add_choose ℝ (a := k) (b := n))
  rw [hchoose, hf]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  field_simp

private theorem choose_two_sq (n : ℕ) :
    ((n + 2).choose 2 : ℝ) ^ 2 =
      6 * ((n + 4).choose 4 : ℝ) - 6 * ((n + 3).choose 3 : ℝ) + (n + 2).choose 2 := by
  simp only [choose_eq_prod, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [Nat.factorial]
  ring

/-- The series defining a local factor has the expected rational closed form. -/
theorem localFactor_closedForm (p : Nat.Primes) :
    let q : ℝ := (p : ℕ)
    localFactor p = (1 - q⁻¹) ^ 4 * (1 + 4 / q + 1 / q ^ 2) := by
  let q : ℝ := (p : ℕ)
  let r := q⁻¹
  have hq : 1 < q := Nat.one_lt_cast.mpr p.2.one_lt
  have hr₀ : 0 < r := inv_pos.mpr (zero_lt_one.trans hq)
  have hr₁ : r < 1 := inv_lt_one_of_one_lt₀ hq
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr₀] using hr₁
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have h3 := hasSum_choose_mul_geometric_of_norm_lt_one 3 hr
  have h4 := hasSum_choose_mul_geometric_of_norm_lt_one 4 hr
  have hsum : HasSum (fun n : ℕ => ((n + 2).choose 2 : ℝ) ^ 2 * r ^ n)
      (6 * (1 / (1 - r) ^ 5) - 6 * (1 / (1 - r) ^ 4) + 1 / (1 - r) ^ 3) := by
    apply (((h4.mul_left (6 : ℝ)).sub (h3.mul_left (6 : ℝ))).add h2).congr_fun
    intro n
    rw [choose_two_sq]
    ring
  change (1 - r) ^ 9 * (∑' n : ℕ, ((n + 2).choose 2 : ℝ) ^ 2 * r ^ n) =
    (1 - r) ^ 4 * (1 + 4 / q + 1 / q ^ 2)
  rw [hsum.tsum_eq, div_eq_mul_inv 4 q, one_div (q ^ 2), ← inv_pow]
  change (1 - r) ^ 9 * (6 * (1 / (1 - r) ^ 5) - 6 * (1 / (1 - r) ^ 4)
    + 1 / (1 - r) ^ 3) = (1 - r) ^ 4 * (1 + 4 * r + r ^ 2)
  have h : 1 - r ≠ 0 := (sub_pos.mpr hr₁).ne'
  field_simp
  ring

private theorem localFactor_pos (p : Nat.Primes) : 0 < localFactor p := by
  let q : ℝ := (p : ℕ)
  have hq : 1 < q := Nat.one_lt_cast.mpr p.2.one_lt
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have h : 0 < 1 - q⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)
  rw [localFactor_closedForm]
  exact mul_pos (pow_pos h 4) (by positivity)

private theorem summable_localFactor_sub_one : Summable (fun p : Nat.Primes => localFactor p - 1) := by
  have hp (k : ℕ) (hk : 1 < k) :
      Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ)⁻¹ ^ k) := by
    simpa only [Function.comp_apply, inv_pow] using
      (Real.summable_nat_pow_inv.mpr hk).comp_injective Nat.Primes.coe_nat_injective
  apply ((((hp 6 (by decide)).sub ((hp 4 (by decide)).mul_left 9)).add
    ((hp 3 (by decide)).mul_left 16)).sub ((hp 2 (by decide)).mul_left 9)).congr
  intro p
  rw [localFactor_closedForm, div_eq_mul_inv 4, one_div, ← inv_pow]
  ring

private theorem summable_log_localFactor :
    Summable (fun p : Nat.Primes => Real.log (localFactor p)) := by
  refine (Real.summable_log_one_add_of_summable summable_localFactor_sub_one).congr ?_
  intro p
  congr 1
  ring

/-- The prime product in the normalization converges. -/
theorem a3_multipliable : Multipliable (fun p : Nat.Primes => localFactor p) :=
  Real.multipliable_of_summable_log localFactor_pos summable_log_localFactor

/-- The prime product in the normalization is positive. -/
theorem a3_pos : 0 < a3 := by
  rw [a3, ← Real.rexp_tsum_eq_tprod localFactor_pos summable_log_localFactor]
  exact Real.exp_pos _

theorem c3_pos : 0 < c3 := by
  exact div_pos a3_pos (by exact_mod_cast Nat.factorial_pos 9)

end ZetaSixth
