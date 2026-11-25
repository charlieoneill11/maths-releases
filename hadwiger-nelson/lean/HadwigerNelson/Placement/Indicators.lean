import HadwigerNelson.Placement.Coordinates
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The colour indicators and permutations used to unfold a monochromatic event. -/

open HadwigerNelson.Wave
open scoped BigOperators

namespace HadwigerNelson.Placement

noncomputable section

def classHit (W : Datum) (c : Label) (z z' : Plane) : ℝ :=
  if Wave.colour W z = some c ∧ Wave.colour W z' = some c then 1 else 0

theorem map_eq_some_inj {f : Label → Label} (hf : Function.Injective f) (s : Option Label)
    (c : Label) : s.map f = some (f c) ↔ s = some c := by
  cases s <;> simp [hf.eq_iff]

theorem hit_pullback (W : Datum) (g : Plane → Plane) (lab : Label → Label)
    (hinj : Function.Injective lab) (hmove : ∀ z, Wave.colour W (g z) = (Wave.colour W z).map lab)
    (c : Label) (z z' : Plane) : classHit W (lab c) (g z) (g z') = classHit W c z z' := by
  simp only [classHit, hmove, map_eq_some_inj hinj]

theorem tau_inj (k : ℤ) : Function.Injective (tauLabel k) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  simpa [tauLabel] using h

theorem sigma1_inj : Function.Injective sigma1Label := by
  apply Function.LeftInverse.injective (g := sigma1Label)
  rintro ⟨b,k⟩
  cases b <;> simp [sigma1Label]

theorem sigma2_inj : Function.Injective sigma2Label := by
  apply Function.LeftInverse.injective (g := sigma2Label)
  rintro ⟨b,k⟩
  cases b <;> simp [sigma2Label, add_assoc] <;> decide +revert

theorem labelOrbit (c : Label) : ∃ k : Fin 3,
    c = tauLabel k.val (false,0) ∨ c = tauLabel k.val (sigma2Label (false,0)) := by decide +revert

theorem sum_indicators {R : Type*} [AddCommMonoidWithOne R] (a b : Option Label) :
  (if a.isSome = true ∧ a=b then (1 : R) else 0) =
    ∑ c : Label, if a=some c ∧ b=some c then (1:R) else 0 := by
  cases a with
  | none => simp
  | some i =>
    cases b with
    | none => simp
    | some j =>
      by_cases h : i = j
      · subst j
        simp
      · have hz (c : Label) : ¬(i = c ∧ j = c) := fun hc ↦ h (hc.1.trans hc.2.symm)
        simp [h, hz]

end
end HadwigerNelson.Placement
