import Legendre.Cosine
import Legendre.Geometry

namespace Legendre

open Finset
open scoped BigOperators

noncomputable def shoulderPrimes (w : Window) : Finset ℕ := by
  classical
  exact (Finset.range (⌊w.endpoint twelveMode.K⌋₊ + 1)).filter
    (fun p : ℕ ↦ p.Prime ∧ 1 < |w.scale p| ∧ |w.scale p| ≤ twelveMode.K)

noncomputable def shoulderPrefix (w : Window) (j : ℕ) : Finset ℕ := by
  classical
  exact (shoulderPrimes w).filter (fun p : ℕ ↦ |w.scale p| ≤ 1 + (j : ℝ) / 4000)

theorem mem_shoulderPrimes (w : Window) (p : ℕ) :
    p ∈ shoulderPrimes w ↔ p < ⌊w.endpoint twelveMode.K⌋₊ + 1 ∧
      p.Prime ∧ 1 < |w.scale p| ∧ |w.scale p| ≤ twelveMode.K := by
  classical
  simp [shoulderPrimes]

theorem mem_shoulderPrefix (w : Window) (j p : ℕ) :
    p ∈ shoulderPrefix w j ↔ p ∈ shoulderPrimes w ∧ |w.scale p| ≤ 1 + (j : ℝ) / 4000 := by
  classical
  simp [shoulderPrefix]

noncomputable def shoulderDrop (e : ℕ → ℚ) (j : ℕ) : ℝ := (e j : ℝ) - (e (j + 1) : ℝ)

theorem shoulderDrop_nonneg (e : ℕ → ℚ) (he : ShoulderSteps e) {j : ℕ} (hj : j ∈ Icc 1 4000) :
    0 ≤ shoulderDrop e j := by
  rcases mem_Icc.mp hj with ⟨hlo, hhi⟩
  exact sub_nonneg.mpr (Rat.cast_le.mpr (he.antitone j hlo hhi))

private theorem sum_drop_Ico (e : ℕ → ℚ) {l r : ℕ} (hlr : l ≤ r) :
    (∑ j ∈ Ico l r, shoulderDrop e j) = (e l : ℝ) - (e r : ℝ) := by
  simp_rw [shoulderDrop, show ∀ j, (e j : ℝ) - (e (j + 1) : ℝ) =
    -((e (j + 1) : ℝ) - (e j : ℝ)) from fun _ ↦ (neg_sub _ _).symm]
  rw [sum_neg_distrib, sum_Ico_sub (fun j ↦ (e j : ℝ)) hlr, neg_sub]

theorem sum_shoulderDrop (e : ℕ → ℚ) (he : ShoulderSteps e) {l : ℕ} (hl : l ≤ 4000) :
    (∑ j ∈ Icc l 4000, shoulderDrop e j) = (e l : ℝ) := by
  have hIcc : Icc l 4000 = Ico l 4001 := by
    ext j
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hIcc, sum_drop_Ico e (hl.trans (by decide)), he.last, Rat.cast_zero, sub_zero]

private theorem shoulder_by_layers (e : ℕ → ℚ) (he : ShoulderSteps e) {s : ℝ} (hs₁ : 1 < s)
    (hs₂ : s ≤ 2) :
    twelveMode.positivePart s ≤ ∑ j ∈ Icc (1 : ℕ) 4000,
      if s ≤ 1 + (j : ℝ) / 4000 then shoulderDrop e j else 0 := by
  classical
  let t := 4000 * (s - 1)
  let i : ℕ := ⌈t⌉₊
  have ht : 0 < t := by dsimp [t]; exact mul_pos (by norm_num) (sub_pos.mpr hs₁)
  have hi₀ : 1 ≤ i := Nat.ceil_pos.mpr ht
  have hi₁ : i ≤ 4000 := Nat.ceil_le.mpr (by dsimp [t]; linarith)
  have hi₁' : 1 + ((i : ℝ) - 1) / 4000 < s := by
    have h := Nat.ceil_lt_add_one ht.le
    change (i : ℝ) < t + 1 at h
    dsimp [t] at h
    linarith
  have h' (j : ℕ) : s ≤ 1 + (j : ℝ) / 4000 ↔ i ≤ j := by
    rw [show i = ⌈t⌉₊ from rfl, Nat.ceil_le]
    dsimp [t]
    constructor <;> intro h <;> linarith
  have hi₂' := (h' i).mpr le_rfl
  have hfilter : (Icc 1 4000).filter (fun j : ℕ ↦ s ≤ 1 + (j : ℝ) / 4000) = Icc i 4000 := by
    ext j
    simp only [mem_filter, mem_Icc, h']
    omega
  rw [← sum_filter, hfilter, sum_shoulderDrop e he hi₁]
  exact he.majorizes i hi₀ hi₁ s hi₁' hi₂'

theorem shoulderSum_le_layers (w : Window) (e : ℕ → ℚ) (he : ShoulderSteps e) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ p ∈ shoulderPrimes w, Real.log p / Real.sqrt (p : ℝ) ≤ B) :
    shoulderSum w twelveMode ≤ B * ∑ j ∈ Icc 1 4000, shoulderDrop e j * (shoulderPrefix w j).card := by
  classical
  have hEven : Function.Even twelveMode.positivePart := fun s ↦ by
    simp only [CosineTest.positivePart, twelveMode.G_even s]
  change (∑ p ∈ shoulderPrimes w, Real.log p / Real.sqrt (p : ℝ) *
    twelveMode.positivePart (w.scale p)) ≤ _
  calc
    _ ≤ ∑ p ∈ shoulderPrimes w, B * (∑ j ∈ Icc (1 : ℕ) 4000,
        if |w.scale p| ≤ 1 + (j : ℝ) / 4000 then shoulderDrop e j else 0) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨_, _, hlo, hhi⟩ := (mem_shoulderPrimes w p).mp hp
      change |w.scale p| ≤ 2 at hhi
      have hnonneg : 0 ≤ twelveMode.positivePart (w.scale p) := le_max_right _ _
      have hG : twelveMode.positivePart (w.scale p) = twelveMode.positivePart |w.scale p| := by
        by_cases h : 0 ≤ w.scale p
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg (lt_of_not_ge h), hEven _]
      apply (mul_le_mul_of_nonneg_right (hb p hp) hnonneg).trans
      rw [hG]
      exact mul_le_mul_of_nonneg_left (shoulder_by_layers e he hlo hhi) hB
    _ = B * (∑ j ∈ Icc (1 : ℕ) 4000, ∑ p ∈ shoulderPrimes w,
        if |w.scale p| ≤ 1 + (j : ℝ) / 4000 then shoulderDrop e j else 0) := by
      rw [← mul_sum, sum_comm]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      change (∑ _p ∈ shoulderPrefix w j, shoulderDrop e j) = _
      simp only [sum_const, nsmul_eq_mul, mul_comm]

end Legendre
