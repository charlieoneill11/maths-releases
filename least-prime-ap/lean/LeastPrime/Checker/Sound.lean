import LeastPrime.Checker.FinalGap
import LeastPrime.Checker.Base

/-! Soundness of the complete directed-rounding checker. -/

namespace LeastPrime.Checker

open MeasureTheory Set

private theorem integration_step (bound : Bound) (j : Nat) (T : GridSet) (hT : Valid T)
    (gap : GridSet → Nat → Nat → Nat)
    (hGap : ∀ passed rest a b, T = passed.reverse ++ rest → a ≤ b → b ≤ unit →
      (∀ I ∈ passed, I.2 ≤ a) → (∀ I ∈ rest, b ≤ I.1) →
        Bounds bound (area (gap passed a b))
          (∫ r in Icc (grid a) (grid b), probabilityFor bound j (residualTarget r (denote T)))) :
    Bounds bound (grid (quotient bound (integrateTarget gap [] 0 T) unit))
      (probabilityFor bound (j + 1) (denote T)) := by
  have hclosed := isClosedTarget_denote hT.1
  rw [probabilityFor_recursion bound j hclosed hT.2.2]
  apply (final_rounding bound _).trans
  exact integrateTarget_correct bound _ gap hT
    (probabilityFor_residual_integrable bound j hclosed hT.2.2)
    (fun r hr hpos => probabilityFor_residual_one bound j hpos hr) hGap

theorem probabilityBound_sound (bound : Bound) (k : Nat) (targets : GridSet) (hT : Valid targets) :
    Bounds bound (grid (probabilityBound bound k targets)) (probabilityFor bound k (denote targets)) := by
  induction k using Nat.strong_induction_on generalizing targets with
  | h k ih =>
    by_cases hk : k < 2
    · exact probabilityBound_base bound k targets hk hT
    cases targets with
    | nil =>
      change Bounds bound (grid (probabilityBound bound k [])) (probabilityFor bound k ∅)
      rw [probabilityBound.eq_1, grid_zero, probabilityFor_empty]
      exact Bounds.refl _ _
    | cons I rest =>
      by_cases h0 : I.1 = 0
      · have hmem : (0 : ℝ) ∈ denote (I :: rest) := by
          exact mem_denote.mpr ⟨I, List.mem_cons_self,
            ⟨by rw [h0, grid_zero], grid_nonneg _⟩⟩
        have heq : probabilityBound bound k (I :: rest) = unit := by
          rw [probabilityBound.eq_def]
          simp only [h0, if_true]
        rw [heq, grid_unit, probabilityFor_zero_mem bound k hmem]
        exact Bounds.refl _ _
      · have hT0 : 0 ∉ denote (I :: rest) := by
          rwa [zero_mem_denote_iff_head_zero hT]
        obtain ⟨n, rfl⟩ : ∃ n : Nat, k = n + 2 := ⟨k - 2, by omega⟩
        cases n with
        | zero =>
          rw [probabilityBound, if_neg h0]
          exact integration_step bound 1 (I :: rest) hT (finalGap bound)
            (fun _ _ _ _ ht hab hb hp hq => finalGap_correct bound ht hT hT0 hab hb hp hq)
        | succ n =>
          change Bounds bound (grid (probabilityBound bound (n + 3) (I :: rest)))
            (probabilityFor bound (n + 3) (denote (I :: rest)))
          rw [probabilityBound, if_neg h0]
          let step := quotient .upper unit (bins bound (n + 3)) - 1
          have hRec : ∀ S, Valid S →
              Bounds bound (grid (probabilityBound bound (n + 2) S)) (probabilityFor bound (n + 2) (denote S)) :=
            fun S hS => ih (n + 2) (by omega) S hS
          exact integration_step bound (n + 2) (I :: rest) hT
            (higherGap bound step (probabilityBound bound (n + 2)))
            (fun _ _ _ _ ht hab hb hp hq =>
              higherGap_correct bound (n + 2) _ step ht hT hT0 hab hb hp hq hRec)

end LeastPrime.Checker

namespace LeastPrime

open Checker

theorem lowerP_sound (k : Nat) (T : GridSet) (hT : Valid T) :
    (lowerP k T : ℝ) ≤ 1000000 * p k (denote T) := by
  have h : grid (probabilityBound .lower k T) ≤ p k (denote T) :=
    probabilityBound_sound .lower k T hT
  have hr := (div_le_iff₀ unit_real_pos).mp h
  simpa [lowerP, unit, mul_comm] using hr

theorem upperQ_sound (k : Nat) (T : GridSet) (hT : Valid T) :
    1000000 * q k (denote T) ≤ (upperQ k T : ℝ) := by
  have h : q k (denote T) ≤ grid (probabilityBound .upper k T) :=
    probabilityBound_sound .upper k T hT
  have hr := (le_div_iff₀ unit_real_pos).mp h
  simpa [upperQ, unit, mul_comm] using hr

end LeastPrime
