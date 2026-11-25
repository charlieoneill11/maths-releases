import HadwigerNelson.Stars.AngularPhase
import HadwigerNelson.Stars.PartitionBounds

/-! Telescoping the four ordered quadrants turns local endpoint primitive
estimates into estimates on the complete angular period. -/

namespace HadwigerNelson.Stars.BoxCheck

theorem fullTurn_lower (src : Angular.Box) (other : Nat) (F : Nat → Int → Int → Nat → ℝ)
    (G : ℝ → ℝ)
    (bound : ∀ q < 4, ∀ a b, a < b → b ≤ resolution →
      changeOf F (nodeSpan src other q a b) ≤ G (endpoint q b)-G (endpoint q a)) :
    spanEval (runs src other) (changeOf F) ≤ G (2*Real.pi)-G 0 := by
  rw [runs_eval]
  have part (q : Nat) (hq : q < 4) :
      leafEval src other q (changeOf F) 17 0 ≤ G (endpoint q resolution)-G (endpoint q 0) := by
    exact leafEval_lower _ _ _ (fun i => G (endpoint q i)) _ (bound q hq) 17 0 (by decide)
  have h0 := part 0 (by decide)
  have h1 := part 1 (by decide)
  have h2 := part 2 (by decide)
  have h3 := part 3 (by decide)
  rw [endpoint_edge,endpoint_zero] at h0
  rw [endpoint_edge] at h1 h2
  rw [endpoint_full] at h3
  linarith

theorem fullTurn_error {B : Type*} [SeminormedAddCommGroup B]
    (src : Angular.Box) (other : Nat) (F : Nat → Int → Int → Nat → B)
    (E : Nat → Int → Int → Nat → ℝ) (G : ℝ → B)
    (bound : ∀ q < 4, ∀ a b, a < b → b ≤ resolution →
      ‖G (endpoint q b)-G (endpoint q a)-changeOf F (nodeSpan src other q a b)‖ ≤
        changeOf E (nodeSpan src other q a b)) :
    ‖G (2*Real.pi)-G 0-spanEval (runs src other) (changeOf F)‖ ≤
      spanEval (runs src other) (changeOf E) := by
  rw [runs_eval,runs_eval]
  let f (q : Nat) := leafEval src other q (changeOf F) 17 0
  let e (q : Nat) := leafEval src other q (changeOf E) 17 0
  let err (q : Nat) := G (endpoint q resolution)-G (endpoint q 0)-f q
  have part (q : Nat) (hq : q < 4) : ‖err q‖ ≤ e q :=
    leafEval_error _ _ _ (fun i => G (endpoint q i)) _ _ (bound q hq) 17 0 (by decide)
  have split : G (2*Real.pi)-G 0-(f 0+f 1+f 2+f 3) = err 0+err 1+err 2+err 3 := by
    simp only [err]
    rw [endpoint_full,endpoint_edge 2,endpoint_edge 1,endpoint_edge 0,endpoint_zero]
    norm_num only [Nat.reduceAdd]
    abel
  rw [split]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (part 0 (by decide)) (part 1 (by decide))))
      (part 2 (by decide)))) (part 3 (by decide)))

end HadwigerNelson.Stars.BoxCheck
