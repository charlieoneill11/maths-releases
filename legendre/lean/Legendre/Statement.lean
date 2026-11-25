import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Legendre

/-- Theorem 1 of the paper. -/
def MainStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ ((11 : ℝ) / 5) < p ∧
      (p : ℝ) < ((n : ℝ) + 1) ^ ((11 : ℝ) / 5)

/-- Theorem 2 of the paper. -/
def SquaresStatement : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ 10 ^ 14 →
    ∃ p : ℕ, p.Prime ∧ m ^ 2 < p ∧ p < (m + 1) ^ 2

/-- Theorem 4 of the paper. -/
def OuterStatement : Prop :=
  ∀ x : ℝ, 35 * 10 ^ 12 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x ^ ((11 : ℝ) / 5) < p ∧
      (p : ℝ) < (x + 1) ^ ((11 : ℝ) / 5)

private theorem rpow_eleven_fifths_pow_five {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((11 : ℝ) / 5)) ^ (5 : ℕ) = x ^ (11 : ℕ) := by
  rw [← Real.rpow_mul_natCast hx]
  rw [show ((11 : ℝ) / 5) * (↑(5 : ℕ) : ℝ) = ↑(11 : ℕ) by norm_num, Real.rpow_natCast]

/-- Lemma 7, the exact integer test for membership in the open power interval. -/
theorem powerInterval_iff (n p : ℕ) :
    ((n : ℝ) ^ ((11 : ℝ) / 5) < p ∧ (p : ℝ) < ((n : ℝ) + 1) ^ ((11 : ℝ) / 5)) ↔
      n ^ 11 < p ^ 5 ∧ p ^ 5 < (n + 1) ^ 11 := by
  have h₁ := pow_lt_pow_iff_left₀ (n := 5)
    (Real.rpow_nonneg (Nat.cast_nonneg n) ((11 : ℝ) / 5)) (Nat.cast_nonneg p) (by decide)
  have h₂ := pow_lt_pow_iff_left₀ (n := 5)
    (Nat.cast_nonneg (α := ℝ) p)
    (Real.rpow_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) ((11 : ℝ) / 5)) (by decide)
  rw [← h₁, ← h₂, rpow_eleven_fifths_pow_five (by positivity),
    rpow_eleven_fifths_pow_five (by positivity)]
  constructor <;> rintro ⟨h₃, h₄⟩ <;> exact ⟨by exact_mod_cast h₃, by exact_mod_cast h₄⟩

/-- Lemma 7, an integral endpoint of a power interval cannot be prime. -/
theorem powerEndpoint_ne_prime (n p : ℕ) (hp : p.Prime) :
    (n : ℝ) ^ ((11 : ℝ) / 5) ≠ p := by
  intro h
  have hpow := congrArg (fun t : ℝ ↦ t ^ (5 : ℕ)) h
  change ((n : ℝ) ^ ((11 : ℝ) / 5)) ^ (5 : ℕ) = (p : ℝ) ^ (5 : ℕ) at hpow
  rw [rpow_eleven_fifths_pow_five (by positivity)] at hpow
  have hnat : n ^ 11 = p ^ 5 := by exact_mod_cast hpow
  have hfactor := congrArg (fun k : ℕ ↦ k.factorization p) hnat
  change (n ^ 11).factorization p = (p ^ 5).factorization p at hfactor
  rw [Nat.factorization_pow, Nat.factorization_pow_self hp, Finsupp.smul_apply, nsmul_eq_mul]
    at hfactor
  omega

/-- Theorem 1 at `n = 1`, with the witness `2`. -/
theorem main_one :
    ∃ p : ℕ, p.Prime ∧ (1 : ℝ) ^ ((11 : ℝ) / 5) < p ∧
      (p : ℝ) < (1 + 1 : ℝ) ^ ((11 : ℝ) / 5) := by
  exact ⟨2, Nat.prime_two, by exact_mod_cast (powerInterval_iff 1 2).2 (by decide)⟩

/-- At the cutoff of Theorem 4, exponent one gives an interval with no natural number. -/
theorem outer_exponent_one_counterexample :
    ¬ ∃ p : ℕ, (35 * 10 ^ 12 : ℝ) ^ (1 : ℝ) < p ∧
      (p : ℝ) < ((35 * 10 ^ 12 : ℝ) + 1) ^ (1 : ℝ) := by
  rintro ⟨p, hlo, hhi⟩
  simp only [Real.rpow_one] at hlo hhi
  have hlo' : 35 * 10 ^ 12 < p := by exact_mod_cast hlo
  have hhi' : p < 35 * 10 ^ 12 + 1 := by exact_mod_cast hhi
  omega

end Legendre
