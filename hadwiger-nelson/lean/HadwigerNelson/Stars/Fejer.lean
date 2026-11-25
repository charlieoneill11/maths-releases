import HadwigerNelson.Stars.Threshold
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace HadwigerNelson.Stars
open Finset
open scoped ComplexConjugate

/-- Summing by diagonals in the square of frequency indices 0,…,K. -/
private theorem sum_diagonals (f : ℕ → ℝ) (K : ℕ) :
    (∑ a ∈ range (K + 1), ∑ b ∈ range (K + 1), f (a - b + (b - a))) =
    (K + 1 : ℝ) * f 0 + 2 * ∑ k ∈ range K, ((K : ℝ) - k) * f (k + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have row : (∑ a ∈ range (K + 1), f ((K+1) - a + (a - (K+1)))) =
        ∑ a ∈ range (K+1), f (a+1) := by
      rw [← sum_range_reflect (fun a => f (a+1)) (K+1)]
      apply sum_congr rfl
      intro a ha
      have := mem_range.mp ha
      congr 1
      omega
    have col : (∑ a ∈ range (K + 1), f (a - (K+1) + ((K+1) - a))) =
        ∑ a ∈ range (K+1), f (a+1) := by simpa [Nat.add_comm] using row
    have weights : (∑ k ∈ range K, ((K + 1 : ℝ) - k) * f (k+1)) =
        (∑ k ∈ range K, ((K : ℝ) - k) * f (k+1)) + ∑ k ∈ range K, f (k+1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro k _
      ring
    rw [sum_range_succ (fun a => ∑ b ∈ range (K+1+1), f (a-b+(b-a))) (K+1)]
    simp_rw [sum_range_succ (fun b => f (_-b+(b-_))) (K+1)]
    rw [sum_add_distrib, ih, row, col]
    push_cast
    rw [sum_range_succ (fun k => ((K:ℝ)+1-k)*f (k+1)) K, weights,
      sum_range_succ (fun a => f (a+1)) K]
    simp only [Nat.sub_self, Nat.zero_add]
    ring

private theorem normSq_sum {α : Type*} (I : Finset α) (f : α → ℂ) :
    Complex.normSq (∑ i ∈ I, f i) = ∑ i ∈ I, ∑ j ∈ I, (f i * conj (f j)).re := by
  have h := congrArg Complex.re (Complex.mul_conj (∑ i ∈ I, f i))
  rw [sum_comm (f := fun i j => (f i * conj (f j)).re)]
  simpa only [map_sum, sum_mul, mul_sum, Complex.re_sum, Complex.ofReal_re] using h.symm

private theorem phase_difference {z : ℂ} (hz : Complex.normSq z = 1) {a b : ℕ}
    (h : a ≤ b) : z^a * (conj z)^b = (conj z)^(b-a) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [pow_add, ← mul_assoc, ← mul_pow, Complex.mul_conj, hz]

private theorem normSq_power_difference {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ i, Complex.normSq (z i) = 1) (a b : ℕ) :
    Complex.normSq (∑ i, (z i)^a * (conj (z i))^b) =
    Complex.normSq (∑ i, (z i)^(a-b+(b-a))) := by
  rcases le_total a b with hab | hba
  · simp only [phase_difference (hz _) hab, Nat.sub_eq_zero_of_le hab, Nat.zero_add]
    rw [← Complex.normSq_conj (∑ i, z i ^ (b-a))]
    simp
  · have elim (i : Fin d) : z i ^ a * (conj (z i))^b = z i^(a-b) := by
      have h := phase_difference (z := conj (z i)) (by simpa using hz i) hba
      simpa [mul_comm] using h
    simp only [elim, Nat.sub_eq_zero_of_le hba, Nat.add_zero]

/-- The same finite Gram sum expanded in frequency indices or vertex indices. -/
private theorem gram_sum {d : ℕ} (z : Fin d → ℂ) (K : ℕ) :
    (∑ i, ∑ j, Complex.normSq (∑ a ∈ range (K+1), (z i * conj (z j))^a)) =
      ∑ a ∈ range (K+1), ∑ b ∈ range (K+1),
        Complex.normSq (∑ i, (z i)^a * (conj (z i))^b) := by
  let R := range (K+1)
  let I : Finset (Fin d) := univ
  let F := fun (ij : Fin d × Fin d) (ab : ℕ × ℕ) =>
    (((z ij.1 * conj (z ij.2))^ab.1) * conj ((z ij.1 * conj (z ij.2))^ab.2)).re
  calc
    _ = ∑ ij ∈ I ×ˢ I, ∑ ab ∈ R ×ˢ R, F ij ab := by
      simp only [I, R, F, sum_product, normSq_sum]
    _ = ∑ ab ∈ R ×ˢ R, ∑ ij ∈ I ×ˢ I, F ij ab := sum_comm
    _ = _ := by
      simp only [I, R, F, sum_product, normSq_sum, map_mul, map_pow, RingHomCompTriple.comp_apply,
        mul_pow, mul_assoc, mul_left_comm]

/-- Fejér's inequality in unnormalised power sums, prior to division by d²(K+1).
The unit phases may coincide. -/
theorem fejer_unnormalised {d : ℕ} (z : Fin d → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1)
    (K : ℕ) :
    (d : ℝ) * (K + 1 : ℝ)^2 ≤
      (K+1 : ℝ) * (d : ℝ)^2 +
        2 * ∑ k ∈ range K, ((K : ℝ) - k) * Complex.normSq (∑ i, (z i)^(k+1)) := by
  have diagonal (i : Fin d) :
      (K + 1 : ℝ)^2 ≤ ∑ j, Complex.normSq (∑ a ∈ range (K+1), (z i * conj (z j))^a) := by
    have h := single_le_sum (s := (univ : Finset (Fin d)))
      (f := fun j => Complex.normSq (∑ a ∈ range (K+1), (z i * conj (z j))^a))
      (fun j _ => Complex.normSq_nonneg _) (mem_univ i)
    simpa [Complex.mul_conj, hz, Complex.normSq_apply, pow_two] using h
  have h := sum_le_sum (s := (univ : Finset (Fin d))) (fun i _ => diagonal i)
  rw [gram_sum] at h
  simp_rw [normSq_power_difference z hz] at h
  rw [sum_diagonals (fun k => Complex.normSq (∑ i, (z i)^k))] at h
  simpa [Complex.normSq_apply, pow_two] using h

/-- Lemma 22 for unit complex phases. The squared magnitude of the normalised
k-th power sum is its squared modulus divided by d². -/
theorem fejer_bound {d : ℕ} (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∀ i, Complex.normSq (z i) = 1) (K : ℕ) :
    (K + 1 : ℝ) / d - 1 ≤ ∑ k : Fin K, fejerWeight K k *
      (Complex.normSq (∑ i, z i ^ (k.val+1)) / (d : ℝ)^2) := by
  have h := fejer_unnormalised z hz K
  rw [← Fin.sum_univ_eq_sum_range (fun k => ((K : ℝ) - k) *
    Complex.normSq (∑ i, (z i)^(k+1))) K] at h
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hK : 0 < (K : ℝ) + 1 := by exact_mod_cast Nat.succ_pos K
  let C := ((K : ℝ)+1) * (d : ℝ)^2
  have hC : 0 < C := mul_pos hK (sq_pos_of_pos hd')
  apply (le_of_mul_le_mul_right _ hC)
  have hlhs : ((K+1 : ℝ)/d-1)*C = (d : ℝ)*(K+1)^2 - (K+1)*(d:ℝ)^2 := by
    unfold C
    field_simp
  rw [hlhs, sum_mul]
  calc
    _ ≤ 2 * ∑ k : Fin K, ((K : ℝ) - k.val) * Complex.normSq (∑ i, z i ^ (k.val+1)) := by linarith
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      unfold fejerWeight C
      field_simp
      ring

end HadwigerNelson.Stars
