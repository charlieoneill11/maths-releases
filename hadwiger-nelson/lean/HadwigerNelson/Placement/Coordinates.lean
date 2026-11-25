import HadwigerNelson.Wave.Geometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Rotations and translations of the Euclidean wave under a random-placement parameter. -/

namespace HadwigerNelson.Placement

noncomputable section

abbrev Translation := ℝ × ℝ
abbrev Sample := ℝ × Translation

def rotate (θ : ℝ) (x : Plane) : Plane :=
  Wave.point (Real.cos θ * x 0 - Real.sin θ * x 1) (Real.sin θ * x 0 + Real.cos θ * x 1)

def place (ω : Sample) (x : Plane) : Plane := rotate ω.1 x + Wave.point ω.2.1 ω.2.2

def colour (W : Wave.Datum) (ω : Sample) (x : Plane) : Option Wave.Label := Wave.colour W (place ω x)

/-- Indicator of two equal nonblank colours, taking values in the reals for integration. -/
def sameColour (W : Wave.Datum) (x y : Plane) : ℝ :=
  if (Wave.colour W x).isSome = true ∧ Wave.colour W x = Wave.colour W y then 1 else 0

@[fun_prop]
theorem continuous_point {α : Type*} [TopologicalSpace α] {u y : α → ℝ}
    (hu : Continuous u) (hy : Continuous y) : Continuous (fun a ↦ Wave.point (u a) (y a)) := by
  have h : Continuous (fun a ↦ ![u a, y a]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> assumption
  exact (PiLp.continuous_toLp ..).comp h

@[fun_prop]
theorem continuous_place (x : Plane) : Continuous (fun ω ↦ place ω x) := by
  unfold place rotate
  fun_prop

def translationPoint (t : Translation) : Plane := Wave.point t.1 t.2

@[fun_prop]
theorem continuous_translationPoint : Continuous translationPoint :=
  continuous_point continuous_fst continuous_snd

end
end HadwigerNelson.Placement
