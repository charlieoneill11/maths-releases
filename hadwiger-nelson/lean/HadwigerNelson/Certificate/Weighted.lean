import HadwigerNelson.Certificate.Enclosure
import HadwigerNelson.Blueprint.Point.Budgets

namespace HadwigerNelson.Certificate.ParameterBoxes

open Crossings

@[simp] theorem real_const (q : ℚ) : (Operations.constant q : ℝ) = q := rfl
@[simp] theorem real_root (x : ℝ) : Operations.root x = Real.sqrt x := rfl
@[simp] theorem real_floor (x : ℝ) : Operations.intPart x = (⌊x⌋:ℤ) := rfl

theorem variance_eq (x : ℝ) : variance x = varianceBound 10689 2090 x := by
  norm_num [variance, pair, four, order, varianceBound, sampledLower, pairProbability, fourProbability]
  ring

theorem weighted_eq (m : ℕ) (s j : ℝ) (a b : ℚ) :
    weighted (m:ℝ) (variance (m:ℝ)) s j a b = weightedBound 10689 m s j a b := by
  simp only [weighted,real_const,real_root,weightedBound,variance_eq,Rat.cast_add,Rat.cast_mul]
  norm_num [order]
  congr 1
  · ring
  · congr 1
    ring

theorem pairLower_eq (m : ℕ) : pairLower (m:ℝ) = Centres.pairLower 10689 m := by
  unfold pairLower Centres.pairLower Centres.retainedArcBound
  simp only [real_const,real_floor]
  norm_num [pair,four,order,pairProbability,fourProbability]
  apply congrArg (fun x : ℝ => ⌊x⌋)
  ring

theorem chooseTwo_eq (s : ℕ) : chooseTwo (s:ℝ) = (s.choose 2 : ℕ) := by
  induction s with
  | zero => norm_num [chooseTwo]
  | succ s h =>
    rw [Nat.choose_succ_succ',Nat.choose_one_right]
    push_cast
    change chooseTwo ((s:ℝ)+1) = (s:ℝ)+(s.choose 2:ℕ)
    rw [← h]
    norm_num [chooseTwo]
    ring

end HadwigerNelson.Certificate.ParameterBoxes
