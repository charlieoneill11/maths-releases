import HadwigerNelson.Centres.Parameters
import HadwigerNelson.Placement.Coordinates
import HadwigerNelson.Wave.Holes.Definitions

namespace HadwigerNelson.Centres
open Set
noncomputable section
attribute [local instance] Classical.propDecidable

def width (W : Wave.Datum) (y : ℝ) : ℝ := if |y| ≤ W.y0 then W.left |y| else 0

def angleBins (p : Profile) : ℕ := if p = .coarse then 32 else 100
def heightBins (p : Profile) : ℕ := if p = .coarse then 48 else 180
def angleStep (p : Profile) (l : ℝ) := cone p l/angleBins p
def heightStep (p : Profile) := (9/1000:ℝ)/heightBins p
def angleBin (p : Profile) (l t : ℝ) : ℕ :=
  max 1 (min (angleBins p) ⌈|t|/angleStep p l⌉₊)

def rectangleHalfWidth (W : Wave.Datum) (p : Profile) (l : ℝ) (i k : ℕ) :=
  let t := i*angleStep p l
  let y := k*heightStep p
  let a := 1-Real.sqrt (1-(smallUpper p l)^2/4)+t^2/2
  let b := a+w^2/2
  max 0 (min (width W (y+heightStep p+a)-t)
    (smallLower p l/2-width W (max 0 (y-b))-b*t))

/-- The symmetric rectangles for a small chord, at orientation offset t. -/
def smallRegion (W : Wave.Datum) (p : Profile) (l t : ℝ) : Set Plane :=
  {z | ∃ k : Fin (heightBins p),
    |z 0| < rectangleHalfWidth W p l (angleBin p l t) k.val ∧
    |z 1| ∈ Icc (k.val*heightStep p) (k.val*heightStep p+heightStep p)}

def centreEvent (W : Wave.Datum) (X D : Finset Plane) (p : Profile) (θ : ℝ)
    (v u : Plane) : Set Placement.Translation :=
  {τ | candidate X D p θ v u ∧ ∃ i j : ℤ, let ζ := Wave.holeLatticePoint W i j
    if chord u v ≤ 2/100 then ∃ t, |t| ≤ cone p (chord u v) ∧ aligned θ t v u ∧
      Placement.place (θ,τ) (midpoint u v)-ζ ∈ smallRegion W p (chord u v) t
    else Placement.place (θ,τ) v-ζ ∈ Wave.hole W ∧
      Placement.place (θ,τ) u-ζ-Wave.point 0 2 ∈ Wave.hole W}

end
end HadwigerNelson.Centres
