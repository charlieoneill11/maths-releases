import LeastPrime.Checker.SliceData
import LeastPrime.Checker.CertificateSound

/-! Soundness and recombination of the additive level-six certificates. -/

namespace LeastPrime.Checker

open MeasureTheory Set

/-- Splitting at a cell boundary leaves the cells and their clipped or full widths unchanged. -/
theorem sumGridCells_split (cell : Nat → Nat → Nat) (step a b k : Nat)
    (h : a + k * (step + 1) ≤ b) :
    let c := a + k * (step + 1)
    sumGridCells cell step a b = sumGridCells cell step a c + sumGridCells cell step c b := by
  induction k generalizing a with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
    have hself : sumGridCells cell step a a = 0 := by
      rw [sumGridCells, dif_neg (Nat.lt_irrefl _)]
    rw [hself, zero_add]
  | succ k ih =>
    let d := a + (step + 1)
    let c := a + (k + 1) * (step + 1)
    have hc : c = d + k * (step + 1) := by
      simp only [c, d, Nat.add_mul, Nat.one_mul]
      omega
    have had : a < d := by dsimp [d]; omega
    have hdc : d ≤ c := by omega
    have hcb : c ≤ b := h
    have hdb : d ≤ b := hdc.trans hcb
    have step_eq (z : Nat) (hdz : d ≤ z) :
        sumGridCells cell step a z = cell a d + sumGridCells cell step d z := by
      rw [sumGridCells, dif_pos (had.trans_le hdz), min_eq_left hdz]
    change sumGridCells cell step a b = sumGridCells cell step a c + sumGridCells cell step c b
    rw [step_eq b hdb, step_eq c hdc, Nat.add_assoc]
    rw [hc] at hcb ⊢
    rw [ih d hcb]

private theorem lowerSliceValue_split (tail : Bool) (a b left right k : Nat)
    (h : left + k * 2223 ≤ right) :
    let mid := left + k * 2223
    lowerSliceValue tail a b left right =
      lowerSliceValue tail a b left mid + lowerSliceValue tail a b mid right := by
  have hstep : lowerSixStep + 1 = 2223 := by decide
  unfold lowerSliceValue higherGap
  have hne : (lowerSlicePassed tail a b).isEmpty = false := by cases tail <;> rfl
  simp only [hne, Bool.false_eq_true, if_false]
  have h' : left + k * (lowerSixStep + 1) ≤ right := by simpa only [hstep] using h
  simpa only [hstep] using
    sumGridCells_split (fun l r => (r - l) *
      probabilityBound .lower 5 (scaledTarget .lower (lowerSlicePassed tail a b) l r))
      lowerSixStep left right k h'

theorem lowerSliceValue_sound {tail : Bool} {a b left right : Nat}
    (ha : 0 < a) (hab : a ≤ b) (hsep : b < unit - b)
    (hl : (lowerSliceGap tail a b).1 ≤ left) (hlr : left ≤ right)
    (hr : right ≤ (lowerSliceGap tail a b).2) :
    area (lowerSliceValue tail a b left right) ≤
      ∫ r in Icc (grid left) (grid right), p 5 (residualTarget r (denote (symmetricWindow a b))) := by
  let T := symmetricWindow a b
  have hT : Valid T := valid_symmetricWindow hab hsep
  have h0 : 0 ∉ denote T := (zero_mem_denote_iff_head_zero hT).not.mpr ha.ne'
  have hrec (S : GridSet) (hS : Valid S) :=
    probabilityBound_sound .lower 5 S hS
  cases tail
  · change b ≤ left at hl
    change right ≤ unit - b at hr
    have hp : ∀ I ∈ ([(a, b)] : GridSet), I.2 ≤ left := by simpa using hl
    have hq : ∀ I ∈ ([(unit - b, unit - a)] : GridSet), right ≤ I.1 := by simpa using hr
    exact higherGap_correct .lower 5 (probabilityBound .lower 5) lowerSixStep (T := T) (passed := [(a, b)]) (rest := [(unit - b, unit - a)])
      rfl hT h0 hlr (hr.trans (Nat.sub_le ..)) hp hq hrec
  · change unit - a ≤ left at hl
    change right ≤ unit at hr
    have hp : ∀ I ∈ ([(unit - b, unit - a), (a, b)] : GridSet), I.2 ≤ left := by
      intro I hI
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl
      · exact hl
      · exact (hsep.le.trans (Nat.sub_le_sub_left hab _)).trans hl
    exact higherGap_correct .lower 5 (probabilityBound .lower 5) lowerSixStep (T := T) (passed := [(unit - b, unit - a), (a, b)]) (rest := [])
      rfl hT h0 hlr hr hp (by simp) hrec

theorem checkLowerSlice_sound {tail : Bool} {a b left right expected : Nat}
    (h : checkLowerSlice tail a b left right expected = true) :
    area expected ≤
      ∫ r in Icc (grid left) (grid right), p 5 (residualTarget r (denote (symmetricWindow a b))) := by
  simp only [checkLowerSlice, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [← h.2]
  exact lowerSliceValue_sound h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1
    h.1.2.2.2.2.1 h.1.2.2.2.2.2

private theorem probabilityBound_wholeGaps {a b : Nat} (ha : 0 < a) (hab : a ≤ b)
    (hsep : b < unit - b) :
    probabilityBound .lower 6 (symmetricWindow a b) =
      quotient .lower (2 * (b - a) * unit + lowerSliceValue false a b b (unit - b) +
        lowerSliceValue true a b (unit - a) unit) unit := by
  rw [symmetricWindow, probabilityBound.eq_def]
  simp only [ha.ne', if_false, integrateTarget, width]
  change quotient .lower
    (0 + (b - a) * unit + (lowerSliceValue false a b b (unit - b) +
      (unit - a - (unit - b)) * unit + lowerSliceValue true a b (unit - a) unit)) unit = _
  have hb : b ≤ unit := hsep.le.trans (Nat.sub_le ..)
  have hw : unit - a - (unit - b) = b - a := by omega
  rw [hw, Nat.mul_assoc, Nat.two_mul, Nat.zero_add]
  refine congrArg (fun n => quotient .lower n unit) ?_
  ac_rfl

private theorem lowerSliceValue_three (tail : Bool) (a b left right k : Nat)
    (h : left + (k + k) * 2223 ≤ right) :
    lowerSliceValue tail a b left right =
      lowerSliceValue tail a b left (left + k * 2223) +
      (lowerSliceValue tail a b (left + k * 2223) (left + (k + k) * 2223) +
        lowerSliceValue tail a b (left + (k + k) * 2223) right) := by
  have hcut : left + k * 2223 + k * 2223 = left + (k + k) * 2223 := by
    rw [Nat.add_mul, Nat.add_assoc]
  have hi₂ : left + k * 2223 + k * 2223 ≤ right := by rwa [hcut]
  have hi₁ : left + k * 2223 ≤ right := (Nat.le_add_right ..).trans hi₂
  have hs₁ := lowerSliceValue_split tail a b left right k hi₁
  have hs₂ := lowerSliceValue_split tail a b (left + k * 2223) right k hi₂
  dsimp only at hs₁ hs₂
  rw [hcut] at hs₂
  rw [hs₁, hs₂]

/-- The six slices give exactly the same rounded value as the unpartitioned computation. -/
theorem probabilityBound_sixSlices {a b : Nat} (ha : 0 < a) (hab : a ≤ b)
    (hsep : b < unit - b) (hi : b + 180 * 2223 ≤ unit - b)
    (ht : unit - a + 44 * 2223 ≤ unit) :
    probabilityBound .lower 6 (symmetricWindow a b) =
      lowerSliceRound a b
        (lowerSliceValue false a b b (b + 90 * 2223))
        (lowerSliceValue false a b (b + 90 * 2223) (b + 180 * 2223))
        (lowerSliceValue false a b (b + 180 * 2223) (unit - b))
        (lowerSliceValue true a b (unit - a) (unit - a + 22 * 2223))
        (lowerSliceValue true a b (unit - a + 22 * 2223) (unit - a + 44 * 2223))
        (lowerSliceValue true a b (unit - a + 44 * 2223) unit) := by
  have hsI := lowerSliceValue_three false a b b (unit - b) 90 hi
  have hsT := lowerSliceValue_three true a b (unit - a) unit 22 ht
  rw [probabilityBound_wholeGaps ha hab hsep, hsI, hsT, lowerSliceRound]
  refine congrArg (fun n => quotient .lower n unit) ?_
  ac_rfl

private theorem lowerSlice_eq_of_check {tail : Bool} {a b left right expected : Nat}
    (h : checkLowerSlice tail a b left right expected = true) :
    lowerSliceValue tail a b left right = expected := by
  simp only [checkLowerSlice, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- Recombine valid additive certificates and certify the resulting probability bound. -/
theorem checkLowerSixSlices_sound {a b x₁ x₂ x₃ y₁ y₂ y₃ : Nat} (ha : 0 < a) (hab : a ≤ b)
    (hsep : b < unit - b) (hi : b + 180 * 2223 ≤ unit - b)
    (ht : unit - a + 44 * 2223 ≤ unit)
    (hx₁ : checkLowerSlice false a b b (b + 90 * 2223) x₁ = true)
    (hx₂ : checkLowerSlice false a b (b + 90 * 2223) (b + 180 * 2223) x₂ = true)
    (hx₃ : checkLowerSlice false a b (b + 180 * 2223) (unit - b) x₃ = true)
    (hy₁ : checkLowerSlice true a b (unit - a) (unit - a + 22 * 2223) y₁ = true)
    (hy₂ : checkLowerSlice true a b (unit - a + 22 * 2223) (unit - a + 44 * 2223) y₂ = true)
    (hy₃ : checkLowerSlice true a b (unit - a + 44 * 2223) unit y₃ = true) :
    grid (lowerSliceRound a b x₁ x₂ x₃ y₁ y₂ y₃) ≤ p 6 (denote (symmetricWindow a b)) := by
  have h := probabilityBound_sixSlices ha hab hsep hi ht
  rw [lowerSlice_eq_of_check hx₁, lowerSlice_eq_of_check hx₂, lowerSlice_eq_of_check hx₃,
    lowerSlice_eq_of_check hy₁, lowerSlice_eq_of_check hy₂, lowerSlice_eq_of_check hy₃] at h
  rw [← h]
  exact probabilityBound_sound .lower 6 (symmetricWindow a b) (valid_symmetricWindow hab hsep)

end LeastPrime.Checker
