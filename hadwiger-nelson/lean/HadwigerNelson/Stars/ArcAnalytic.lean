import HadwigerNelson.Stars.ArcTable
import HadwigerNelson.Arithmetic.Angle
import HadwigerNelson.Arithmetic.Pi

/-! Exact angular interpretation of the prefix table, and the directed π
normalisation for positive and negative signed values. -/

namespace HadwigerNelson.Stars.BoxCheck
open Arithmetic

noncomputable def phaseAngle (i : Nat) : ℝ :=
  2*(phaseScale : ℝ)*Real.arctan ((i : ℝ)/resolution)

theorem arcStep_bounds (i : Nat) :
    ((arcStep i).low : ℝ) ≤ phaseAngle (i+1)-phaseAngle i ∧
    phaseAngle (i+1)-phaseAngle i ≤ (arcStep i).high := by
  have h := moment_bin_enclosure (resolution : Int) (i : Int) phaseScale (by decide) (by positivity) (by decide)
  dsimp only [phaseAngle,arcStep]
  rw [←mul_sub]
  simpa only [Int.cast_natCast,Nat.cast_add,Nat.cast_one] using h

/-- Formula for the width of every certified dyadic or merged span. -/
theorem actual_spanArc_bounds (s : Span) (hle : s.start ≤ s.stop) (hhi : s.stop ≤ resolution) :
    ((spanArc arcTable s).low : ℝ) ≤ phaseAngle s.stop-phaseAngle s.start ∧
    phaseAngle s.stop-phaseAngle s.start ≤ (spanArc arcTable s).high :=
  spanArc_bounds phaseAngle arcStep_bounds s hle hhi

theorem normalise_sound (m k : Int) (hk : 0 < k) :
    ((normalise m k : Int) : ℝ)/quant ≤ (m : ℝ)/((k : ℝ)*phaseScale*Real.pi) := by
  have p := moment_scaled_d20_le m quant (k*phaseScale) (mul_pos hk (by decide)) (by decide)
  have eq : signedScale m quant (k*phaseScale*314159265358979323846)
      (k*phaseScale*314159265358979323847) (10^20) = normalise m k := by
    by_cases hm : m < 0 <;> simp [normalise,signedScale,hm,piLow,piDen]
  rw [eq,Int.cast_mul] at p
  apply (div_le_iff₀ (by norm_num [quant] : (0 : ℝ) < quant)).2
  convert p using 1 <;> ring

end HadwigerNelson.Stars.BoxCheck
