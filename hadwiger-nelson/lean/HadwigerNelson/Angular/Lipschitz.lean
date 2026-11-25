import HadwigerNelson.Angular.Datum
import HadwigerNelson.Wave.Geometry.GridBounds
import HadwigerNelson.Wave.Geometry.PeriodicLipschitz

namespace HadwigerNelson.CompleteWave

private def slopeBlock (k : Nat) : Prop := ∀ i : Fin 256,
  let j := k*256+i.val
  ordinate (j+1) ≤ ordinate j + step ∧ ordinate j ≤ ordinate (j+1) + step

private instance (k : Nat) : Decidable (slopeBlock k) := by unfold slopeBlock; infer_instance

set_option maxRecDepth 12000 in
private theorem slope0 : slopeBlock 0 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem slope1 : slopeBlock 1 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem slope2 : slopeBlock 2 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem slope3 : slopeBlock 3 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem slope4 : slopeBlock 4 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem slope5 : slopeBlock 5 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem slope6 : slopeBlock 6 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem slope7 : slopeBlock 7 := by decide +kernel

private theorem knot_slope (j : Nat) (hj : j < 2048) :
    ordinate (j+1) ≤ ordinate j + step ∧ ordinate j ≤ ordinate (j+1) + step := by
  have all (k : Fin 8) : slopeBlock k := by
    fin_cases k
    · exact slope0
    · exact slope1
    · exact slope2
    · exact slope3
    · exact slope4
    · exact slope5
    · exact slope6
    · exact slope7
  have h := all ⟨j/256,by omega⟩ ⟨j%256,Nat.mod_lt _ (by decide)⟩
  simpa only [show j/256*256+j%256=j by omega] using h

/-- The complete-wave right boundary is 1-Lipschitz across knots
and across seams of its periodic extension. -/
theorem right_lipschitz (s t : ℝ) :
    |Wave.completeDatum.right s - Wave.completeDatum.right t| ≤ |s-t| := by
  apply Wave.periodic_lipschitz Wave.completeDatum.right_periodic _ s t
  intro a ha b hb
  rw [Wave.completeDatum_right ha,Wave.completeDatum_right hb]
  let v (i : Nat) := (ordinate i : ℝ)/scale
  have bound (i : Nat) (hi : i < 2048) : |v (i+1)-v i| ≤ 1/4096 := by
    obtain ⟨inc,dec⟩ := knot_slope i hi
    have up : (ordinate (i+1) : ℝ) ≤ ordinate i + (244140625:ℝ) := by exact_mod_cast inc
    have dn : (ordinate i : ℝ) ≤ ordinate (i+1) + (244140625:ℝ) := by exact_mod_cast dec
    rw [abs_le]
    norm_num [v,scale]
    constructor <;> linarith
  have arg (x : ℝ) (hx : x ∈ Set.Icc 0 Wave.H) : 4096*x ∈ Set.Icc 0 (2048:ℝ) := by
    obtain ⟨lo,hi⟩ := hx
    unfold Wave.H at hi
    constructor <;> linarith
  have h := Angular.Grid.interpolation_lipschitz v 2048 (by decide) (1/4096) bound (arg a ha) (arg b hb)
  rw [← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4096)] at h
  change |Angular.Grid.interpolation v 2048 _ - Angular.Grid.interpolation v 2048 _| ≤ _
  linarith

end HadwigerNelson.CompleteWave
