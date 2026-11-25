import LeastPrime.Checker.Compute
import LeastPrime.Quadrature
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Cast.Order.Field

/-! Directed rounding at the endpoints of a level-two integration cell. -/

namespace LeastPrime.Checker

open MeasureTheory Set

private theorem unit_pos : 0 < (unit : ℝ) := by norm_num [unit]

theorem quotient_lower_le (n d : ℕ) : (quotient .lower n d : ℝ) ≤ (n : ℝ) / d :=
  Nat.cast_div_le

theorem le_quotient_upper {n d : ℕ} (hd : 0 < d) :
    (n : ℝ) / d ≤ (quotient .upper n d : ℝ) := by
  have heq : n ⌈/⌉ d = quotient .upper n d := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    unfold quotient
    congr 1
    omega
  have h := (ceilDiv_le_iff_le_mul hd).mp (le_rfl : n ⌈/⌉ d ≤ n ⌈/⌉ d)
  rw [heq, Nat.mul_comm] at h
  exact (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr (by exact_mod_cast h)

private theorem scaled_lower (n d : ℕ) :
    (quotient .lower (n * unit) d : ℝ) / unit ≤ (n : ℝ) / d := by
  apply (div_le_iff₀ unit_pos).mpr
  have h := quotient_lower_le (n * unit) d
  push_cast at h
  convert h using 1
  ring

private theorem scaled_upper {n d : ℕ} (hd : 0 < d) :
    (n : ℝ) / d ≤ (quotient .upper (n * unit) d : ℝ) / unit := by
  apply (le_div_iff₀ unit_pos).mpr
  have h := le_quotient_upper (n := n * unit) hd
  push_cast at h
  convert h using 1
  ring

private theorem midpoint_lower (a b ga gb : ℕ) :
    (midpoint .lower a b ga gb : ℝ) / unit ≤ ((ga : ℝ) + gb) / (a + b) := by
  simpa only [midpoint, Nat.cast_add] using scaled_lower (ga + gb) (a + b)

private theorem midpoint_upper {a b ga gb : ℕ} (ha : 0 < a) :
    ((ga : ℝ) + gb) / (a + b) ≤ (midpoint .upper a b ga gb : ℝ) / unit := by
  simpa only [midpoint, Nat.cast_add] using
    scaled_upper (n := ga + gb) (d := a + b) (by omega)

private theorem trapezoid_lower (a b ga gb : ℕ) :
    (trapezoid .lower a b ga gb : ℝ) / unit ≤ ((ga : ℝ) / a + (gb : ℝ) / b) / 2 := by
  let l := quotient .lower (ga * unit) a
  let r := quotient .lower (gb * unit) b
  have hl : (l : ℝ) / unit ≤ (ga : ℝ) / a := scaled_lower ga a
  have hr : (r : ℝ) / unit ≤ (gb : ℝ) / b := scaled_lower gb b
  have h := div_le_div_of_nonneg_right (quotient_lower_le (l + r) 2) unit_pos.le
  push_cast at h
  change (quotient .lower (l + r) 2 : ℝ) / unit ≤ _
  calc
    _ ≤ (((l : ℝ) + r) / 2) / unit := h
    _ = ((l : ℝ) / unit + (r : ℝ) / unit) / 2 := by ring
    _ ≤ _ := by linarith only [hl, hr]

private theorem trapezoid_upper {a b ga gb : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((ga : ℝ) / a + (gb : ℝ) / b) / 2 ≤ (trapezoid .upper a b ga gb : ℝ) / unit := by
  let l := quotient .upper (ga * unit) a
  let r := quotient .upper (gb * unit) b
  have hl : (ga : ℝ) / a ≤ (l : ℝ) / unit := scaled_upper ha
  have hr : (gb : ℝ) / b ≤ (r : ℝ) / unit := scaled_upper hb
  have h := div_le_div_of_nonneg_right
    (le_quotient_upper (n := l + r) (by decide : 0 < (2 : ℕ))) unit_pos.le
  push_cast at h
  change _ ≤ (quotient .upper (l + r) 2 : ℝ) / unit
  calc
    _ ≤ ((l : ℝ) / unit + (r : ℝ) / unit) / 2 := by linarith only [hl, hr]
    _ = (((l : ℝ) + r) / 2) / unit := by ring
    _ ≤ _ := h

/-- Level two's rounded midpoint or trapezoid contribution bounds the integral on one affine
piece. The endpoint lengths `ga` and `gb` and the cell coordinates are in grid units. -/
theorem estimatedProbability_bounds {a b ga gb : ℕ} {g : ℝ → ℝ} {α β : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hg : ∀ r ∈ Icc ((a : ℝ) / unit) ((b : ℝ) / unit), g r = α * r + β)
    (hga : g ((a : ℝ) / unit) = (ga : ℝ) / unit)
    (hgb : g ((b : ℝ) / unit) = (gb : ℝ) / unit) :
    let A := (a : ℝ) / unit
    let B := (b : ℝ) / unit
    (B - A) * ((estimatedProbability .lower a b ga gb : ℝ) / unit) ≤
      (∫ r in Icc A B, g r / r) ∧
      (∫ r in Icc A B, g r / r) ≤
        (B - A) * ((estimatedProbability .upper a b ga gb : ℝ) / unit) := by
  let A := (a : ℝ) / unit
  let B := (b : ℝ) / unit
  let f (r : ℝ) := α + β / r
  have hb : 0 < b := by omega
  have ha' : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  have hA : 0 < A := div_pos ha' unit_pos
  have hB : 0 < B := div_pos hb' unit_pos
  have hAB : A < B := (div_lt_div_iff_of_pos_right unit_pos).mpr (by exact_mod_cast hab)
  have hlen : 0 ≤ B - A := sub_nonneg.mpr hAB.le
  have haI : A ∈ Icc A B := ⟨le_rfl, hAB.le⟩
  have hbI : B ∈ Icc A B := ⟨hAB.le, le_rfl⟩
  have hval : EqOn (fun r => g r / r) f (Icc A B) := by
    intro r hr
    have hr0 : r ≠ 0 := (hA.trans_le hr.1).ne'
    show g r / r = α + β / r
    rw [hg r hr, add_div, mul_div_cancel_right₀ _ hr0]
  have hint := setIntegral_congr_fun (μ := volume) measurableSet_Icc hval
  have hfa : f A = (ga : ℝ) / a := by
    rw [← hval haI]
    change g ((a : ℝ) / unit) / A = _
    rw [hga]
    change ((ga : ℝ) / unit) / ((a : ℝ) / unit) = _
    field_simp [ha'.ne', unit_pos.ne']
  have hfb : f B = (gb : ℝ) / b := by
    rw [← hval hbI]
    change g ((b : ℝ) / unit) / B = _
    rw [hgb]
    change ((gb : ℝ) / unit) / ((b : ℝ) / unit) = _
    field_simp [hb'.ne', unit_pos.ne']
  have hsum : (ga : ℝ) / unit + (gb : ℝ) / unit = α * (A + B) + 2 * β := by
    rw [← hga, ← hgb, hg A haI, hg B hbI]
    ring
  have hpos : 0 < A + B := add_pos hA hB
  have hmid : f ((A + B) / 2) = ((ga : ℝ) + gb) / (a + b) := by
    calc
      f ((A + B) / 2) = ((ga : ℝ) / unit + (gb : ℝ) / unit) / (A + B) := by
        change α + β / ((A + B) / 2) = _
        rw [hsum]
        field_simp [hpos.ne']
      _ = _ := by
        dsimp only [A, B]
        field_simp [unit_pos.ne', (add_pos ha' hb').ne']
  have hcompare : f B ≤ f A ↔ gb * a ≤ ga * b := by
    rw [hfb, hfa, div_le_div_iff₀ hb' ha']
    exact_mod_cast (Iff.rfl : gb * a ≤ ga * b ↔ gb * a ≤ ga * b)
  change (B - A) * ((estimatedProbability .lower a b ga gb : ℝ) / unit) ≤ _ ∧
    _ ≤ (B - A) * ((estimatedProbability .upper a b ga gb : ℝ) / unit)
  rw [hint]
  by_cases hc : gb * a ≤ ga * b
  · have hβ : 0 ≤ β := (reciprocal_affine_decreasing_iff hA hAB).mp (hcompare.mpr hc)
    obtain ⟨hl, hu⟩ := hermite_hadamard_inv (α := α) hA hAB hβ
    change (B - A) * f ((A + B) / 2) ≤ _ at hl
    change _ ≤ (B - A) * ((f A + f B) / 2) at hu
    rw [hmid] at hl
    rw [hfa, hfb] at hu
    simp [estimatedProbability, hc]
    exact ⟨(mul_le_mul_of_nonneg_left (midpoint_lower a b ga gb) hlen).trans hl,
      hu.trans (mul_le_mul_of_nonneg_left (trapezoid_upper ha hb) hlen)⟩
  · have hβ : β ≤ 0 := le_of_not_ge (fun h => hc (hcompare.mp
      ((reciprocal_affine_decreasing_iff hA hAB).mpr h)))
    obtain ⟨hl, hu⟩ := hermite_hadamard_inv_nonpos (α := α) hA hAB hβ
    change (B - A) * ((f A + f B) / 2) ≤ _ at hl
    change _ ≤ (B - A) * f ((A + B) / 2) at hu
    rw [hfa, hfb] at hl
    rw [hmid] at hu
    simp [estimatedProbability, hc]
    exact ⟨(mul_le_mul_of_nonneg_left (trapezoid_lower a b ga gb) hlen).trans hl,
      hu.trans (mul_le_mul_of_nonneg_left (midpoint_upper ha) hlen)⟩

end LeastPrime.Checker
