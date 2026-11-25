import Legendre.FourierGridData
import Legendre.TwelveQuadrature

namespace Legendre

open Arithmetic MeasureTheory Set
open scoped BigOperators

private theorem fourierNode_cast (j : ℕ) : (fourierNode j : ℝ) = (j : ℝ) / 4000 := by
  simp [fourierNode]

private theorem fourierCell_width (j : ℕ) (hj : 1 ≤ j) :
    (fourierNode j : ℝ) - (fourierNode (j - 1) : ℝ) = 1 / 4000 := by
  rw [fourierNode_cast, fourierNode_cast, Nat.cast_sub hj, Nat.cast_one]
  ring

private theorem fourierCell_lt (j : ℕ) (hj : 1 ≤ j) : (fourierNode (j - 1) : ℝ) < fourierNode j := by
  linarith [fourierCell_width j hj]

theorem cellAbsUpper_sound (j : ℕ) (hj : 1 ≤ j) :
    (∫ t in (fourierNode (j - 1) : ℝ)..(fourierNode j : ℝ), |twelveMode.F t|) ≤
      (cellAbsUpper j : ℝ) / 4000 := by
  have hleft := (Bounds.abs_sound (fourierNodeBounds_sound (j - 1))).2
  have hright := (Bounds.abs_sound (fourierNodeBounds_sound j)).2
  have h := quadrature_mass_cell (fourierCell_lt j hj) twelveMode.F_contDiff_two
    (fun t _ ↦ twelveMode_F_curvature t) hleft hright
  rw [fourierCell_width j hj] at h
  convert h using 1
  push_cast [cellAbsUpper, fourierEpsilon]
  ring

private theorem fourierCell_log (j : ℕ) (hj : 1 ≤ j) :
    (∫ t in (fourierNode (j - 1) : ℝ)..(fourierNode j : ℝ), Real.log t) ≤
      (cellLogIntegralUpper j : ℝ) := by
  rw [integral_log]
  linarith only [cellLogIntegralUpper_sound j, fourierCell_width j hj]

theorem cellLogUpper_sound (j : ℕ) (hj : 1 ≤ j) :
    (∫ t in (fourierNode (j - 1) : ℝ)..(fourierNode j : ℝ), |twelveMode.F t| * Real.log t) ≤
      (cellLogUpper j : ℝ) := by
  let a : ℝ := fourierNode (j - 1)
  let b : ℝ := fourierNode j
  let A := (fourierNodeBounds (j - 1)).abs
  let B := (fourierNodeBounds j).abs
  have hA := Bounds.abs_sound (fourierNodeBounds_sound (j - 1))
  have hB := Bounds.abs_sound (fourierNodeBounds_sound j)
  have hab : a < b := fourierCell_lt j hj
  have hw : b - a = 1 / 4000 := fourierCell_width j hj
  have ha : 0 ≤ a := by dsimp [a]; rw [fourierNode_cast]; positivity
  have hlog : (∫ t in a..b, Real.log t) ≤ (cellLogIntegralUpper j : ℝ) := fourierCell_log j hj
  have heps : (161 : ℝ) * (1 / 4000) ^ 2 / 8 = 161 / (8 * 4000 ^ 2) := by norm_num
  unfold cellLogUpper
  dsimp only
  split_ifs with hpos hsign
  · have hja : (4000 : ℝ) ≤ (j - 1 : ℕ) := by exact_mod_cast (show 4000 ≤ j - 1 by omega)
    have ha' : 1 ≤ a := by dsimp [a]; rw [fourierNode_cast]; linarith
    have h := quadrature_log_cell_pos hab ha' twelveMode.F_contDiff_two
      (fun t _ ↦ twelveMode_F_curvature t) hA.2 hB.2
    rw [hw, heps] at h
    exact h.trans (by
      push_cast [fourierEpsilon]
      apply mul_le_mul_of_nonneg_left hlog
      have hnonneg : 0 ≤ (A.hi : ℝ) := (abs_nonneg _).trans hA.2
      change 0 ≤ max (A.hi : ℝ) (B.hi : ℝ) + _
      exact add_nonneg (hnonneg.trans (le_max_left _ _)) (by norm_num))
  · have hbj : (j : ℝ) ≤ 4000 := by exact_mod_cast (le_of_not_gt hpos)
    have hb : b ≤ 1 := by dsimp [b]; rw [fourierNode_cast]; linarith
    have hsign' : (0 ≤ twelveMode.F a ∧ 0 ≤ twelveMode.F b) ∨
        (twelveMode.F a ≤ 0 ∧ twelveMode.F b ≤ 0) := by
      rcases hsign with hs | hs
      · left
        have hsa : 0 < (fourierNodeBounds (j - 1)).lo := hs.trans_le (min_le_left _ _)
        have hsb : 0 < (fourierNodeBounds j).lo := hs.trans_le (min_le_right _ _)
        exact ⟨((Rat.cast_pos.mpr hsa).trans_le (fourierNodeBounds_sound (j - 1)).1).le,
          ((Rat.cast_pos.mpr hsb).trans_le (fourierNodeBounds_sound j).1).le⟩
      · right
        have hsa : (fourierNodeBounds (j - 1)).hi < 0 := (le_max_left _ _).trans_lt hs
        have hsb : (fourierNodeBounds j).hi < 0 := (le_max_right _ _).trans_lt hs
        exact ⟨((fourierNodeBounds_sound (j - 1)).2.trans_lt (Rat.cast_lt_zero.mpr hsa)).le,
          ((fourierNodeBounds_sound j).2.trans_lt (Rat.cast_lt_zero.mpr hsb)).le⟩
    have h := quadrature_log_cell_neg hab ha hb twelveMode.F_contDiff_two
      (fun t _ ↦ twelveMode_F_curvature t) ((min_le_left _ _).trans hA.1)
      ((min_le_right _ _).trans hB.1) hsign'
    rw [hw, heps] at h
    have hlog' : (∫ t in a..b, Real.log t) ≤ min 0 (cellLogIntegralUpper j : ℝ) := by
      apply le_min _ hlog
      have hn := intervalIntegral.integral_nonneg (μ := volume) (f := fun x ↦ -Real.log x)
        hab.le fun x hx ↦ neg_nonneg.mpr (Real.log_nonpos (ha.trans hx.1) (hx.2.trans hb))
      simpa only [intervalIntegral.integral_neg, neg_nonneg] using hn
    exact h.trans (by
      push_cast [fourierEpsilon]
      apply mul_le_mul_of_nonneg_left hlog' (le_max_left _ _))
  · have hbj : (j : ℝ) ≤ 4000 := by exact_mod_cast (le_of_not_gt hpos)
    have hb : b ≤ 1 := by dsimp [b]; rw [fourierNode_cast]; linarith
    simpa only [Rat.cast_zero] using quadrature_log_cell_nonpos (f := twelveMode.F) hab ha hb

private theorem sum_fourier_cells {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) :
    (∑ j ∈ Finset.Icc 1 64000,
      ∫ t in (fourierNode (j - 1) : ℝ)..(fourierNode j : ℝ), f t) = ∫ t in (0 : ℝ)..16, f t := by
  have hIcc : Finset.Icc (1 : ℕ) 64000 = Finset.Ico 1 64001 := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  let a (j : ℕ) : ℝ := fourierNode (j - 1)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := a)
    (m := 1) (n := 64001) (by decide) (fun j _ ↦ hf (a j) (a (j + 1)))
  have ha₁ : a 1 = 0 := by norm_num [a, fourierNode_cast]
  have ha₂ : a 64001 = 16 := by norm_num [a, fourierNode_cast]
  rw [ha₁, ha₂] at hsum
  rw [hIcc]
  simpa only [a, Nat.add_sub_cancel] using hsum

theorem gridMassUpper_sound :
    (∫ t in (0 : ℝ)..16, |twelveMode.F t|) ≤ (gridMassUpper : ℝ) := by
  rw [← sum_fourier_cells (fun a b ↦ twelveMode.F_contDiff_one.continuous.abs.intervalIntegrable a b)]
  unfold gridMassUpper
  push_cast
  exact Finset.sum_le_sum (fun j hj ↦ cellAbsUpper_sound j (Finset.mem_Icc.mp hj).1)

theorem gridMomentUpper_sound :
    (∫ t in (0 : ℝ)..16, |twelveMode.F t| * Real.log t) ≤ (gridMomentUpper : ℝ) := by
  rw [← sum_fourier_cells (fun a b ↦
    (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).continuousOn_mul
      twelveMode.F_contDiff_one.continuous.abs.continuousOn)]
  unfold gridMomentUpper
  push_cast
  exact Finset.sum_le_sum (fun j hj ↦ cellLogUpper_sound j (Finset.mem_Icc.mp hj).1)

theorem checkGridMass_integral_sound (threshold : ℚ) (h : checkGridMass threshold = true) :
    2 * (∫ t in (0 : ℝ)..16, |twelveMode.F t|) < (threshold : ℝ) :=
  (mul_le_mul_of_nonneg_left gridMassUpper_sound (by norm_num)).trans_lt (checkGridMass_sound threshold h)

theorem checkGridMoment_integral_sound (threshold : ℚ) (h : checkGridMoment threshold = true) :
    2 * (∫ t in (0 : ℝ)..16, |twelveMode.F t| * Real.log t) < (threshold : ℝ) :=
  (mul_le_mul_of_nonneg_left gridMomentUpper_sound (by norm_num)).trans_lt (checkGridMoment_sound threshold h)

end Legendre
