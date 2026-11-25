import HadwigerNelson.Stars.LocalGain

/-! Pointwise domination of the native-minus-alternate sum by the true
locked-star gain, for every list of incident directions. -/

namespace HadwigerNelson.Stars
open scoped BigOperators

noncomputable def labelIndicator {L : Type*} (v : Option L) (a : L) : ℝ := by
  classical exact if v = some a then 1 else 0

private theorem countLabel {L : Type*} {d : Nat} (v : Fin d → Option L) (a : L) :
    (∑ j, labelIndicator (v j) a) =
    (by classical exact ((Finset.univ.filter (fun j => v j = some a)).card : ℝ)) := by
  classical
  exact (Finset.natCast_card_filter _ _).symm

/-- A locked vertex sees the alternate colour and can subtract at most one
from the native-minus-alternate comparison. -/
theorem localGain_ge_signed {L : Type*} {d : Nat} (v : Fin d → Option L) (a b : L) :
    max 0 (∑ j, (labelIndicator (v j) a-labelIndicator (v j) b)) ≤ localGain (some a) v := by
  classical
  apply max_le (localGain_range _ _).1
  rw [Finset.sum_sub_distrib,countLabel,countLabel]
  unfold localGain
  simp only [Option.isSome_some,true_and,eq_comm (a := some a)]
  by_cases locked : ∀ k, ∃ j, v j = some k
  · rw [if_pos locked]
    obtain ⟨j,h⟩ := locked b
    have nz : 0 < (Finset.univ.filter (fun j => v j = some b)).card :=
      Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
    have r : (1 : ℝ) ≤ (Finset.univ.filter (fun j => v j = some b)).card := by exact_mod_cast nz
    linarith
  · rw [if_neg locked]
    have r : (0 : ℝ) ≤ (Finset.univ.filter (fun j => v j = some b)).card := by positivity
    linarith

theorem localGain_ge_native {L : Type*} {d : Nat} (v : Fin d → Option L) (a : L) :
    (∑ j, labelIndicator (v j) a) - 1 ≤ localGain (some a) v := by
  classical
  rw [countLabel]
  unfold localGain
  simp only [Option.isSome_some,true_and,eq_comm (a := some a)]
  split <;> linarith

end HadwigerNelson.Stars
