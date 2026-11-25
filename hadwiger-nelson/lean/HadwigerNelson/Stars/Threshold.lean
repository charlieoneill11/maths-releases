import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace HadwigerNelson.Stars

/-- The index `k` represents harmonic number `k.val + 1`. -/
noncomputable def fejerWeight (K : ℕ) (k : Fin K) : ℝ :=
  2 * (1 - (k.val + 1 : ℝ) / (K + 1 : ℝ))

theorem fejerWeight_nonneg {K : ℕ} (k : Fin K) : 0 ≤ fejerWeight K k := by
  unfold fejerWeight
  have hk : (k.val : ℝ) ≤ K := by exact_mod_cast k.isLt.le
  have hK : 0 < (K : ℝ) + 1 := by exact_mod_cast Nat.succ_pos K
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr ((div_le_one hK).mpr (add_le_add_left hk 1)))

/-- The right hand side of the box estimate in Lemma 23 for one harmonic.
Here `area` is the box area divided by xH and `Z` is the native-box term. -/
noncomputable def boxCredit {ι : Type*} (boxes : Finset ι)
    (area mean amp : ι → ℝ) (Z s : ℝ) : ℝ :=
  Z + ∑ b ∈ boxes, area b * max 0 (mean b + amp b * s)

theorem boxCredit_mono {ι : Type*} (boxes : Finset ι)
    (area mean amp : ι → ℝ) (Z : ℝ)
    (ha : ∀ b ∈ boxes, 0 ≤ area b) (hh : ∀ b ∈ boxes, 0 ≤ amp b) :
    Monotone (boxCredit boxes area mean amp Z) := by
  intro x y hxy
  unfold boxCredit
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro b hb
  exact mul_le_mul_of_nonneg_left
    (max_le_max_left 0 (add_le_add_right (mul_le_mul_of_nonneg_left hxy (hh b hb)) _))
    (ha b hb)

/-- Lemma 24. A successful native-box test or a strict Fejér threshold test
forces the expected per-incidence credit `score` to be at least `β`.
The power sums `s` are represented by their absolute values. -/
theorem threshold_test {ι : Type*} {K d : ℕ} (hK : 0 < K)
    (boxes : Finset ι) (area mean : ι → ℝ) (amp : Fin K → ι → ℝ)
    (t s : Fin K → ℝ) (Z β score : ℝ)
    (ha : ∀ b ∈ boxes, 0 ≤ area b) (hh : ∀ k b, b ∈ boxes → 0 ≤ amp k b)
    (hs : ∀ k, 0 ≤ s k ∧ s k ≤ 1)
    (hbox : ∀ k, boxCredit boxes area mean (amp k) Z (s k) ≤ score)
    (htest : ∀ k, t k = 1 ∨ β ≤ boxCredit boxes area mean (amp k) Z (t k))
    (hfejer : (K + 1 : ℝ) / d - 1 ≤ ∑ k, fejerWeight K k * (s k) ^ 2)
    (hpass : β ≤ Z ∨ (∑ k, fejerWeight K k * (t k) ^ 2) < (K + 1 : ℝ) / d - 1) :
    β ≤ score := by
  rcases hpass with hZ | hthreshold
  · let k : Fin K := ⟨0, hK⟩
    apply hZ.trans (le_trans _ (hbox k))
    unfold boxCredit
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun b hb =>
      mul_nonneg (ha b hb) (le_max_left _ _))
  · by_contra! hsmall
    have hst (k : Fin K) : s k ≤ t k := by
      rcases htest k with ht | ht
      · rw [ht]
        exact (hs k).2
      · by_contra! hlt
        exact (not_le_of_gt hsmall) (ht.trans
          ((boxCredit_mono boxes area mean (amp k) Z ha (hh k) hlt.le).trans (hbox k)))
    have hsum : (∑ k, fejerWeight K k * (s k) ^ 2) ≤
        ∑ k, fejerWeight K k * (t k) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs k).1 (hst k) 2)
        (fejerWeight_nonneg k)
    exact (not_lt_of_ge (hfejer.trans hsum)) hthreshold

end HadwigerNelson.Stars
