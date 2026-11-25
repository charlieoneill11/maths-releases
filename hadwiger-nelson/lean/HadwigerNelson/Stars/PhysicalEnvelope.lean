import HadwigerNelson.Stars.Wall
import HadwigerNelson.Stars.AngularPhase
import HadwigerNelson.Stars.Partition
import HadwigerNelson.Stars.Directions
import HadwigerNelson.Stars.LocalDifference

/-! Each classified dyadic node bounds the actual colour indicators at all
angles in its closed half-angle interval, uniformly over the open source box. -/

namespace HadwigerNelson.Stars.BoxCheck
open Set
open CompleteWave (scale xInt)

theorem gap_complete : (2*(scale : ℝ)) < 3*(2*(xInt : ℝ))-peak := by
  have entry (i : Nat) (hi : i < 2049) : CompleteWave.profile[i]?.getD 0 = CompleteWave.ordinate i := by
    simp [CompleteWave.profile,hi]
  have pk : peak = (CompleteWave.ordinate 1024 : Int) :=
    congrArg Int.ofNat (entry 1024 (by decide))
  have upper := (CompleteWave.ordinate_facts CompleteWave.validProfile (by decide : 1024 ≤ 2048)).2.1
  have h : 2*(scale : Int) < 3*(2*(xInt : Int))-peak := by
    rw [pk]
    norm_num [scale,xInt] at upper ⊢
    omega
  exact_mod_cast h

/-- Geographic horizontal window of every unit displacement from a selected source. -/
private theorem destination_window (z : Plane) (θ : ℝ) (hx : 0 ≤ z 0 ∧ z 0 ≤ 1) :
    -(2*(scale:ℝ)) ≤ scale*(z+direction θ) 0 ∧ scale*(z+direction θ) 0 ≤ 2*(scale:ℝ) := by
  have pos : (0 : ℝ) ≤ scale := by norm_num [scale]
  have h1 : -2 ≤ (z+direction θ) 0 := by
    change -2 ≤ z 0+Real.cos θ
    linarith [Real.neg_one_le_cos θ,hx.1]
  have h2 : (z+direction θ) 0 ≤ 2 := by
    change z 0+Real.cos θ ≤ 2
    linarith [Real.cos_le_one θ,hx.2]
  constructor <;> nlinarith [mul_nonneg pos (sub_nonneg.mpr h1),mul_nonneg pos (sub_nonneg.mpr h2)]

private theorem actual_represents (b : Angular.Box) (c : Nat) (hc : 1 ≤ c ∧ c ≤ 6)
    (z : Plane) (inside : InBox b (scale*z 0) (scale*z 1))
    (win : -(2*(scale:ℝ)) ≤ scale*z 0 ∧ scale*z 0 ≤ 2*(scale:ℝ)) :
    Represents (classify b c) (decide (Wave.colour Wave.completeDatum z = some (actualLabel c))) := by
  classical
  have h := classify_represents completeWallBounds b c (scale*z 0) (scale*z 1) inside win gap_complete
  simpa only [hasCode_iff_colour _ Wave.completeDatum_x Wave.completeDatum_left c hc z] using h

/-- Lower and upper envelopes for the signed response of the physical complete wave. -/
theorem node_envelope (src : Angular.Box) (other : Nat) (hc : 1 ≤ other ∧ other ≤ 6)
    (distinct : actualLabel 1 ≠ actualLabel other) (z : Plane)
    (inside : InBox src (scale*z 0) (scale*z 1)) (xrange : 0 ≤ z 0 ∧ z 0 ≤ 1)
    {q a b : Nat} (hq : q < 4) (hab : a ≤ b) (hb : b ≤ resolution)
    {θ : ℝ} (hθ : θ ∈ Icc (endpoint q a) (endpoint q b)) :
    let s := nodeSpan src other q a b
    let colour := Wave.colour Wave.completeDatum (z+direction θ)
    |2*(labelIndicator colour (actualLabel 1)-labelIndicator colour (actualLabel other))-s.coeff| ≤ s.radius := by
  classical
  let dest := destination src (quadrant q (Angular.halfAngleBox resolution a b))
  have hdest := destination_contains inside (ray_contains hq hab hb hθ)
  have located : InBox dest (scale*(z+direction θ) 0) (scale*(z+direction θ) 1) := by
    convert hdest using 1 <;> simp [direction,mul_add]
  let w := Wave.colour Wave.completeDatum (z+direction θ)
  let n := decide (w = some (actualLabel 1))
  let o := decide (w = some (actualLabel other))
  have hn : Represents (classify dest 1) n :=
    actual_represents dest 1 (by decide) _ located (destination_window z θ xrange)
  have ho : Represents (classify dest other) o :=
    actual_represents dest other hc _ located (destination_window z θ xrange)
  have dis : ¬(n = true ∧ o = true) := by
    rintro ⟨a,b⟩
    exact distinct (Option.some.inj ((of_decide_eq_true a).symm.trans (of_decide_eq_true b)))
  have signed := signedStep_sound (classify dest 1) (classify dest other) n o hn ho dis
  change |2*(labelIndicator w (actualLabel 1)-labelIndicator w (actualLabel other))-
    ((signedStep (classify dest 1) (classify dest other)).1 : ℝ)| ≤
    ((signedStep (classify dest 1) (classify dest other)).2 : ℝ)
  have vals (c : Nat) : labelIndicator w (actualLabel c) =
      (indicator (decide (w = some (actualLabel c))) : ℝ) := by
    by_cases h : w = some (actualLabel c) <;> simp [labelIndicator,indicator,h]
  rw [vals,vals]
  exact_mod_cast signed

end HadwigerNelson.Stars.BoxCheck
