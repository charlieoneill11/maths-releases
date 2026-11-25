import Chowla.StageEvaluation

namespace Chowla.Checker

/-- Verify a reported rational enclosure and its strict comparison. The real
enclosure proof for the evaluator uses the preceding stage as an input. -/
def stageCheck (i : Fin 8) (previous reported : StageBounds) : Bool :=
  decide (evaluateStage i previous = reported) && reported.check i

private theorem stageCheck_result {i : Fin 8} {previous reported : StageBounds}
    (h : stageCheck i previous reported = true) :
    evaluateStage i previous = reported ∧ reported.check i = true := by
  simpa only [stageCheck, Bool.and_eq_true, decide_eq_true_eq] using h

/-- The accepted exact output encloses the model quantities and passes the paper's
strict rational comparison, assuming the corresponding facts for the preceding stage. -/
theorem stageCheck_sound (i : Fin 8) (previous reported : StageBounds)
    (h : stageCheck i previous reported = true)
    (hprev : i.val ≠ 0 → previous.Sound (i - 1) ∧ previous.check (i - 1) = true) :
    reported.Sound i ∧ reported.check i = true := by
  obtain ⟨he, hc⟩ := stageCheck_result h
  refine ⟨?_, hc⟩
  rw [← he]
  fin_cases i
  · exact evaluateStage_zero_sound previous
  · exact evaluateStage_one_sound previous (hprev (by decide)).1 (hprev (by decide)).2
  · exact evaluateStage_two_sound previous (hprev (by decide)).1 (hprev (by decide)).2
  · exact evaluateStage_three_sound previous (hprev (by decide)).1 (hprev (by decide)).2
  · exact evaluateStage_four_sound previous (hprev (by decide)).1 (hprev (by decide)).2
  · exact evaluateStage_five_sound previous (hprev (by decide)).1 (hprev (by decide)).2
  · exact evaluateStage_six_sound previous (hprev (by decide)).1
  · exact evaluateStage_seven_sound previous (hprev (by decide)).1

end Chowla.Checker
