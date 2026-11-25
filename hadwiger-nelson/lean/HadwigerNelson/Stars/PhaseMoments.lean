import HadwigerNelson.Stars.MomentsRuntime
import HadwigerNelson.Arithmetic.Gaussian
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! Rational endpoint phases and the accumulated fixed-point error at one
signed span. All four quadrant rotations preserve the Pythagorean identity. -/

namespace HadwigerNelson.Stars.BoxCheck
open Arithmetic

theorem phaseTriple_spec (q i : Nat) :
    let t := phaseTriple q i
    0 < t.den ∧ t.x*t.x+t.y*t.y = t.den*t.den := by
  have hz : q%4 < 4 := Nat.mod_lt _ (by decide)
  have norm : (0 : Int) < (resolution : Int)*resolution+(i : Int)*i := by
    have hn : (0 : Int) < resolution := by decide
    nlinarith [mul_self_nonneg (i : Int),mul_pos hn hn]
  generalize h : q%4 = r at hz
  interval_cases r <;> simp only [phaseTriple,h] <;> exact ⟨norm,by ring⟩

noncomputable def exactPhase (q i : Nat) : ℂ :=
  let t := phaseTriple q i
  ⟨(t.x : ℝ)/t.den,(t.y : ℝ)/t.den⟩

theorem phase_norm_one (q i : Nat) : ‖exactPhase q i‖ = 1 := by
  have ⟨hd,hs⟩ := phaseTriple_spec q i
  exact GaussianInt.rational_norm_one _ _ _ hd hs

theorem phase_power_error (q i : Nat) (k : Fin harmonics) :
    ‖GaussianInt.value phaseScale (GaussianInt.power phaseScale (phaseBase q i) (k.val+1)) -
      exactPhase q i^(k.val+1)‖ ≤ 6*(k.val+1 : Nat)/(phaseScale : ℝ) := by
  have ⟨hd,hs⟩ := phaseTriple_spec q i
  have b : k.val < 56 := k.isLt
  have : 6*(k.val+1) ≤ 336 := by omega
  have hk : 6*((k.val+1 : Nat) : ℝ) ≤ phaseScale := calc
    _ ≤ (336 : ℝ) := by exact_mod_cast this
    _ ≤ _ := by norm_num [phaseScale]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    GaussianInt.rational_power_error phaseScale _ _ _ (k.val+1) (by decide) hd hs hk

/-- The computed per-span complex contribution before division by k.
Both endpoints together cost 12k ticks, multiplied by the signed mass. -/
theorem span_term_error (table : Array Arc) (s : Span) (k : Fin harmonics) :
    let a := exactPhase s.quadrant s.start^(k.val+1)
    let b := exactPhase s.quadrant s.stop^(k.val+1)
    let m := (prepareSpan table s).term k.val
    ‖GaussianInt.value phaseScale m-(s.coeff : ℂ)*(a-b)‖ ≤
      (s.coeff.natAbs : ℝ)*(12*(k.val+1 : Nat)/(phaseScale : ℝ)) := by
  dsimp only
  by_cases hc : s.coeff = 0
  · simp [prepareSpan,SpanMoments.term,hc,GaussianInt.value]
    rfl
  let u := GaussianInt.power phaseScale (phaseBase s.quadrant s.start) (k.val+1)
  let v := GaussianInt.power phaseScale (phaseBase s.quadrant s.stop) (k.val+1)
  have val : GaussianInt.value phaseScale ((prepareSpan table s).term k.val) =
      (s.coeff : ℂ)*(GaussianInt.value phaseScale u - GaussianInt.value phaseScale v) := by
    apply Complex.ext <;> simp [SpanMoments.term,prepareSpan,hc,GaussianInt.powerTable_get _ _ _ _ k.isLt,
      GaussianInt.value,u,v] <;> ring
  rw [val,←mul_sub,Complex.norm_mul]
  have e := GaussianInt.arc_error phaseScale (k.val+1) (Nat.succ_pos _)
    (GaussianInt.value phaseScale u) (GaussianInt.value phaseScale v)
    (exactPhase s.quadrant s.start^(k.val+1)) (exactPhase s.quadrant s.stop^(k.val+1))
    (phase_power_error _ _ k) (phase_power_error _ _ k)
  have hnorm : ‖(s.coeff : ℂ)‖ = (s.coeff.natAbs : ℝ) := by
    simp
  rw [hnorm]
  have hk : (0 : ℝ) < (k.val+1 : Nat) := by exact_mod_cast Nat.succ_pos k.val
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have e' := (div_le_iff₀ hk).1 e
  simpa only [div_mul_eq_mul_div] using e'

end HadwigerNelson.Stars.BoxCheck
