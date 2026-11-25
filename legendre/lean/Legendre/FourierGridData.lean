import Legendre.Arithmetic.Cos
import Legendre.Arithmetic.Log
import Legendre.TwelveConstants

namespace Legendre

open Arithmetic
open scoped BigOperators

def fourierNode (i : ℕ) : ℚ := (i : ℚ) / 4000

private def fourierFactor (y : ℚ) : ℚ :=
  8 * ∑ j : Fin 12, (-1 : ℚ) ^ j.val * (CosineTest.frequency j : ℚ) * twelveWeight j /
    ((CosineTest.frequency j : ℚ) ^ 2 - (8 * y) ^ 2)

private def reciprocalPi : Bounds := ⟨piBounds.hi⁻¹, piBounds.lo⁻¹⟩

private theorem reciprocalPi_sound : reciprocalPi.Encloses Real.pi⁻¹ := by
  have hp : 0 < (piBounds.lo : ℝ) := by norm_num [piBounds]
  exact ⟨by simpa [reciprocalPi] using inv_anti₀ Real.pi_pos piBounds_sound.2,
    by simpa [reciprocalPi] using inv_anti₀ hp piBounds_sound.1⟩

private def findPole (y : ℚ) : Option (Fin 12) :=
  (List.finRange 12).find? (fun j ↦ decide ((CosineTest.frequency j : ℚ) = 8 * y))

/-- Enclose `F₁₂(i/4000)` using the closed form and the exact values at its removable poles. -/
def fourierNodeBounds (i : ℕ) : Bounds :=
  let y := fourierNode i
  match findPole y with
  | some j => ⟨2 * twelveWeight j, 2 * twelveWeight j⟩
  | none => (((cosPi (4 * y)).mul reciprocalPi).smul (fourierFactor y)).round (10 ^ 18)

theorem fourierNodeBounds_sound (i : ℕ) :
    (fourierNodeBounds i).Encloses (twelveMode.F (fourierNode i)) := by
  unfold fourierNodeBounds
  dsimp only
  cases hp : findPole (fourierNode i) with
  | some j =>
    unfold findPole at hp
    have hj : (CosineTest.frequency j : ℚ) = 8 * fourierNode i := by
      exact of_decide_eq_true (List.find?_some
        (p := fun j : Fin 12 ↦ decide ((CosineTest.frequency j : ℚ) = 8 * fourierNode i)) hp)
    have hj' := congrArg (fun q : ℚ ↦ (q : ℝ)) hj
    push_cast at hj'
    have hy : (fourierNode i : ℝ) = (CosineTest.frequency j : ℝ) / (4 * twelveMode.K) := by
      rw [twelveMode_K]
      linarith
    have hvalue : twelveMode.F (fourierNode i) = 2 * (twelveWeight j : ℝ) :=
      (congrArg twelveMode.F hy).trans (by
        simpa only [twelveMode_K, twelveMode_weight] using twelveMode.F_angular_value j)
    rw [hvalue]
    simp [Bounds.Encloses]
  | none =>
    unfold findPole at hp
    have hn (j : Fin twelveMode.modes) : (CosineTest.frequency j : ℝ) ^ 2 ≠
        (4 * twelveMode.K * (fourierNode i : ℝ)) ^ 2 := by
      intro he
      have hf : 0 ≤ (CosineTest.frequency j : ℝ) := by positivity
      have hy : 0 ≤ (fourierNode i : ℝ) := by unfold fourierNode; push_cast; positivity
      have he' : (CosineTest.frequency j : ℝ) = 8 * (fourierNode i : ℝ) := by
        have h₁ : 0 ≤ (4 * twelveMode.K * (fourierNode i : ℝ)) := by rw [twelveMode_K]; positivity
        have h₂ := le_antisymm ((pow_le_pow_iff_left₀ hf h₁ (by decide : (2 : ℕ) ≠ 0)).mp he.le)
          ((pow_le_pow_iff_left₀ h₁ hf (by decide : (2 : ℕ) ≠ 0)).mp he.ge)
        simpa [twelveMode_K, show (4 : ℝ) * 2 = 8 by norm_num] using h₂
      have hbad : (CosineTest.frequency j : ℚ) = 8 * fourierNode i := by exact_mod_cast he'
      exact (List.find?_eq_none.mp hp j (List.mem_finRange j)) (decide_eq_true hbad)
    have hb := Bounds.round_sound
      (Bounds.smul_sound (fourierFactor (fourierNode i))
        (Bounds.mul_sound (cosPi_sound (4 * fourierNode i)) reciprocalPi_sound))
      (10 ^ 18) (by positivity)
    convert hb using 1
    rw [twelveMode.F_eq_closed_form _ hn]
    simp only [twelveMode_K, twelveMode_weight]
    push_cast [fourierFactor]
    have hh : 2 * Real.pi * 2 * (fourierNode i : ℝ) = Real.pi * (4 * (fourierNode i : ℝ)) := by ring
    rw [hh, show (4 : ℝ) * 2 = 8 by norm_num]
    ring_nf
    rfl

def fourierEpsilon : ℚ := 161 / (8 * 4000 ^ 2)

/-- The average of the two endpoint upper bounds plus the interpolation allowance. -/
def cellAbsUpper (j : ℕ) : ℚ :=
  ((fourierNodeBounds (j - 1)).abs.hi + (fourierNodeBounds j).abs.hi) / 2 + fourierEpsilon

def nodeLogProductBounds (i : ℕ) : Bounds :=
  if i = 0 then ⟨0, 0⟩ else (logBounds (fourierNode i)).smul (fourierNode i)

theorem nodeLogProductBounds_sound (i : ℕ) :
    (nodeLogProductBounds i).Encloses ((fourierNode i : ℝ) * Real.log (fourierNode i)) := by
  by_cases hi : i = 0
  · simp [hi, nodeLogProductBounds, Bounds.Encloses, fourierNode]
  · have hq : 0 < fourierNode i := by
      unfold fourierNode
      exact div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hi)) (by norm_num)
    simpa [nodeLogProductBounds, hi] using
      Bounds.smul_sound (fourierNode i) (logBounds_sound (fourierNode i) hq)

def cellLogIntegralUpper (j : ℕ) : ℚ :=
  (nodeLogProductBounds j).hi - (nodeLogProductBounds (j - 1)).lo - 1 / 4000

theorem cellLogIntegralUpper_sound (j : ℕ) :
    (fourierNode j : ℝ) * Real.log (fourierNode j) -
      (fourierNode (j - 1) : ℝ) * Real.log (fourierNode (j - 1)) - 1 / 4000 ≤
      (cellLogIntegralUpper j : ℝ) := by
  have h := sub_le_sub_right
    (sub_le_sub (nodeLogProductBounds_sound j).2 (nodeLogProductBounds_sound (j - 1)).1)
    (1 / 4000 : ℝ)
  simpa [cellLogIntegralUpper] using h

/-- The contribution of the whole cell to the upper logarithmic moment. -/
def cellLogUpper (j : ℕ) : ℚ :=
  let left := fourierNodeBounds (j - 1)
  let right := fourierNodeBounds j
  let logIntegral := cellLogIntegralUpper j
  if 4000 < j then
    (max left.abs.hi right.abs.hi + fourierEpsilon) * logIntegral
  else if 0 < min left.lo right.lo ∨ max left.hi right.hi < 0 then
    max 0 (min left.abs.lo right.abs.lo - fourierEpsilon) * min 0 logIntegral
  else 0

def gridMassUpper : ℚ := ∑ j ∈ Finset.Icc 1 64000, cellAbsUpper j / 4000

def gridMomentUpper : ℚ := ∑ j ∈ Finset.Icc 1 64000, cellLogUpper j

def checkFourierZero (threshold : ℚ) : Bool :=
  decide (threshold < (fourierNodeBounds 0).lo)

theorem checkFourierZero_sound (threshold : ℚ) (h : checkFourierZero threshold = true) :
    (threshold : ℝ) < twelveMode.F 0 := by
  have h' : threshold < (fourierNodeBounds 0).lo := of_decide_eq_true h
  have hzero := (fourierNodeBounds_sound 0).1
  have hnode : (fourierNode 0 : ℝ) = 0 := by norm_num [fourierNode]
  rw [hnode] at hzero
  exact ((Rat.cast_lt (K := ℝ)).mpr h').trans_le hzero

def checkGridMass (threshold : ℚ) : Bool := decide (2 * gridMassUpper < threshold)

theorem checkGridMass_sound (threshold : ℚ) (h : checkGridMass threshold = true) :
    2 * (gridMassUpper : ℝ) < (threshold : ℝ) := by
  have h' : 2 * gridMassUpper < threshold := of_decide_eq_true h
  simpa using (Rat.cast_lt (K := ℝ)).mpr h'

def checkGridMoment (threshold : ℚ) : Bool := decide (2 * gridMomentUpper < threshold)

theorem checkGridMoment_sound (threshold : ℚ) (h : checkGridMoment threshold = true) :
    2 * (gridMomentUpper : ℝ) < (threshold : ℝ) := by
  have h' : 2 * gridMomentUpper < threshold := of_decide_eq_true h
  simpa using (Rat.cast_lt (K := ℝ)).mpr h'

theorem checkFourierZero_verified : checkFourierZero 1.00000063 = true := by decide +kernel

theorem twelveMode_F_zero_lower : 1.00000063 < twelveMode.F 0 := by
  simpa using checkFourierZero_sound 1.00000063 checkFourierZero_verified

end Legendre
