import HadwigerNelson.Cited
import Mathlib.Tactic.Linarith

namespace HadwigerNelson.Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Probabilities that a uniformly chosen k-subset of n vertices contains a
fixed pair or a fixed ordered collection of four distinct vertices. -/
def pairProbability (n k : ℕ) : ℝ :=
  (k : ℝ) * (k - 1 : ℝ) / ((n : ℝ) * (n - 1 : ℝ))

def fourProbability (n k : ℕ) : ℝ :=
  pairProbability n k * (k - 2 : ℝ) * (k - 3 : ℝ) / ((n - 2 : ℝ) * (n - 3 : ℝ))

def sampledLower (n k : ℕ) (m : ℝ) : ℝ :=
  (6 * m * pairProbability n k - (266 / 9 : ℝ) * (k - 2 : ℝ)) / fourProbability n k

theorem fourProbability_pos {n k : ℕ} (hk : 4 ≤ k) (hkn : k ≤ n) :
    0 < fourProbability n k := by
  have k4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have n4 : (4 : ℝ) ≤ n := by exact_mod_cast hk.trans hkn
  unfold fourProbability pairProbability
  repeat' first | apply div_pos | apply mul_pos
  all_goals linarith


/-- All parallel edges have the same ordered endpoints in the labelled model. -/
def multiplicity {n m : ℕ} (G : Graph n m) (v w : Fin n) : ℕ :=
  (Finset.univ.filter fun e : Fin m => G.left e = v ∧ G.right e = w).card

end
end HadwigerNelson.Crossings
