import Legendre.Interpolation
import Legendre.ShoulderGridData
import Legendre.TwelveConstants

namespace Legendre

open Arithmetic Set
open scoped BigOperators

theorem shoulderNodeUpper_sound (i : ℕ) :
    twelveMode.polynomial ((shoulderNode i : ℚ) : ℝ) ≤ (shoulderNodeUpper i : ℝ) := by
  rw [CosineTest.polynomial_eq_sum]
  unfold shoulderNodeUpper
  push_cast
  apply le_trans _ (le_max_right _ _)
  refine Finset.sum_le_sum fun j _ ↦ ?_
  let q := (CosineTest.frequency j : ℚ) * shoulderNode i / 4
  have hj := (Bounds.smul_sound (twelveWeight j) (cosPi_sound q)).2
  have heq : Real.pi * (q : ℝ) = twelveMode.angularFrequency j * (shoulderNode i : ℝ) := by
    simp only [q, CosineTest.angularFrequency, twelveMode_K]
    push_cast
    ring
  simpa only [heq, twelveMode_weight] using hj

private theorem shoulderLocalHeight_sound (j : ℕ) (hj : 1 ≤ j) (s : ℝ)
    (hs₁ : 1 + ((j : ℝ) - 1) / 4000 < s) (hs₂ : s ≤ 1 + (j : ℝ) / 4000) :
    twelveMode.polynomial s ≤ (shoulderLocalHeight j : ℝ) := by
  let a := (shoulderNode (j - 1) : ℝ)
  let b := (shoulderNode j : ℝ)
  have ha : a = 1 + ((j : ℝ) - 1) / 4000 := by
    simp [a, shoulderNode, Nat.cast_sub hj]
  have hb : b = 1 + (j : ℝ) / 4000 := by simp [b, shoulderNode]
  have hs₁' : a ≤ s := (ha.trans_lt hs₁).le
  have hs₂' : s ≤ b := hb.symm ▸ hs₂
  have hw : b - a = (1 : ℝ) / 4000 := by rw [ha, hb]; ring
  have hab : a < b := by linarith
  have he := linearInterpolation_error hab ⟨hs₁', hs₂'⟩ (twelveMode.contDiff_polynomial)
    (fun y _ ↦ twelveMode_polynomial_curvature y)
  let u := (b - s) / (b - a)
  let v := (s - a) / (b - a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hs₂') (sub_nonneg.mpr hab.le)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hs₁') (sub_nonneg.mpr hab.le)
  have huv : u + v = 1 := by dsimp [u, v]; rw [hw]; linarith
  let m := max (shoulderNodeUpper (j - 1)) (shoulderNodeUpper j)
  have h₁ : twelveMode.polynomial a ≤ (m : ℝ) :=
    (shoulderNodeUpper_sound (j - 1)).trans (Rat.cast_le.mpr (le_max_left _ _))
  have h₂ : twelveMode.polynomial b ≤ (m : ℝ) :=
    (shoulderNodeUpper_sound j).trans (Rat.cast_le.mpr (le_max_right _ _))
  have hmax : u * twelveMode.polynomial a + v * twelveMode.polynomial b ≤ (m : ℝ) := by
    calc
      _ ≤ u * (m : ℝ) + v * (m : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ hu) (mul_le_mul_of_nonneg_left h₂ hv)
      _ = _ := by rw [← add_mul, huv, one_mul]
  have he' : twelveMode.polynomial s -
      (u * twelveMode.polynomial a + v * twelveMode.polynomial b) ≤ 16 * (b - a) ^ 2 / 8 :=
    (le_abs_self _).trans he
  rw [hw] at he'
  have hlocal : (shoulderLocalHeight j : ℝ) = (m : ℝ) + 2 / 4000 ^ 2 := by
    simp [shoulderLocalHeight, m]
  rw [hlocal]
  linarith

/-- The first-height Boolean test suffices for the paper's real step bound. -/
theorem shoulderHeight_steps_of_check (h : checkShoulderHead shoulderHeightTable = true) :
    ShoulderSteps shoulderHeight := by
  refine ⟨fun j _ hj' ↦ shoulderHeight_nonneg j hj', fun j hj hj' ↦ ?_, shoulderHeight_last,
    shoulderHeight_first_of_check h, ?_⟩
  · rw [shoulderHeight_rec j hj hj']
    exact le_max_right _ _
  · intro j hj hj' s hs₁ hs₂
    have hsK : s ∈ Icc (-twelveMode.K) twelveMode.K := by
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have hjR' : (j : ℝ) ≤ 4000 := by exact_mod_cast hj'
      simp only [twelveMode_K, mem_Icc]
      constructor <;> linarith
    have hpol := shoulderLocalHeight_sound j hj s hs₁ hs₂
    unfold CosineTest.positivePart
    rw [twelveMode.G_eq_polynomial hsK]
    apply max_le _ (Rat.cast_nonneg.mpr (shoulderHeight_nonneg j (by omega)))
    apply hpol.trans
    apply Rat.cast_le.mpr
    rw [shoulderHeight_rec j hj hj']
    exact le_max_left _ _

end Legendre
