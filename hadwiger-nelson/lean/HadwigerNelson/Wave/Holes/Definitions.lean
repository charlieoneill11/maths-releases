import HadwigerNelson.Placement.Law
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace HadwigerNelson.Wave
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory Set

/-- Length of intersection of two centred intervals with half-widths a and b
after a horizontal displacement x. -/
def holeSlice (a b x : ℝ) := max 0 (min (2*a) (min (2*b) (a+b-x)))

def holeCovariogram (W : Datum) (v : Plane) : ℝ :=
  volume.real {z : Plane | z ∈ hole W ∧ z-v ∈ hole W}

def bothBlank (W : Datum) (v : Plane) : ℝ :=
  (Placement.translationLaw W).real {τ | let z := point τ.1 τ.2
    colour W z = none ∧ colour W (z+v) = none}

def tickDown (x : ℝ) : ℝ := (⌊x*10^12⌋ : ℤ) / (10^12 : ℝ)
def tickUp (x : ℝ) : ℝ := (⌈x*10^12⌉ : ℤ) / (10^12 : ℝ)

/-- The certificate rounds twice the segment area down in squared picounits. -/
def areaDown (x : ℝ) : ℝ := (⌊2*x*10^24⌋ : ℤ) / (2*10^24 : ℝ)

/-- Area below the positive part of the line interpolating u,v on a unit interval. -/
def positiveChord (u v : ℝ) : ℝ :=
  if 0 ≤ u then
    if 0 ≤ v then (u+v)/2 else u^2/(2*(u-v))
  else if 0 ≤ v then v^2/(2*(v-u)) else 0

/-- Breakpoints include those of both translates of the profile. -/
def holePartition {k : ℕ} (W : Datum) (Y : ℝ) (grid : Fin (k+1) → ℝ) : Prop :=
  grid 0 = Y-W.y0 ∧ grid (Fin.last k) = W.y0 ∧ Monotone grid ∧
  ∀ i : Fin k, ∀ c ∈ ({0,Y} : Set ℝ), ∃ a b : ℝ, ∀ t ∈ Icc (grid i.castSucc) (grid i.succ),
    W.left (t-c) = a*t+b

/-- Definition 18, evaluated on the merged knot list for the rounded displacement. -/
def holeLower {k : ℕ} (W : Datum) (x y : ℝ) (grid : Fin (k+1) → ℝ) : ℝ :=
  let X := tickUp x
  let Y := tickUp y
  let f := fun t =>
    let a := tickDown (W.left t)
    let b := tickDown (W.left (t-Y))
    min (2*a) (min (2*b) (a+b-X))
  if 2*W.y0 ≤ Y then 0 else
    (∑ i : Fin k, areaDown ((grid i.succ - grid i.castSucc) *
      positiveChord (f (grid i.castSucc)) (f (grid i.succ)))) / (2*W.x*H)

/-- A lower enclosure abstracts only the independently bounded area of overlapping holes.
Forest retention and joint blank probabilities are proved from this inequality. -/
def holeEnclosure (W : Datum) (Ω : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, ∀ v : Plane, |v 0| ≤ x → |v 1| ≤ y →
    0 ≤ Ω x y ∧ Ω x y ≤ holeCovariogram W v / (2*W.x*H)

end
end HadwigerNelson.Wave
