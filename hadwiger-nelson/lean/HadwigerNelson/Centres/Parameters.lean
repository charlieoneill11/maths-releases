import HadwigerNelson.Centres.MinorArc
import HadwigerNelson.Crossings.Consecutive
import HadwigerNelson.Placement.Coordinates
import HadwigerNelson.Data.PartialWave

namespace HadwigerNelson.Centres
open Set
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev δR : ℝ := 53/10000
abbrev δ : ℝ := 1837/250000
abbrev w : ℝ := 73/10000

inductive Profile | coarse | fine deriving DecidableEq

def intercept (p : Profile) : ℝ := if p = .coarse then 230/10^10 else 259/10^10
def smallIntercept (p : Profile) : ℝ := if p = .coarse then 79/10^10 else 93/10^10
def angleCost (p : Profile) : ℝ := if p = .coarse then 980/10^10 else 1100/10^10

def mediumBreaks : Finset ℝ :=
  {2/100,4/100,8/100,12/100,16/100,18/100} ∪
    (Finset.range 56).image (fun i : ℕ => (190+(i:ℝ))/1000)

def smallLower (p : Profile) (l : ℝ) : ℝ :=
  if l < δ then (if p = .fine ∧ 6/1000 < l then 6/1000 else δR)
  else if p = .fine ∧ 8/1000 < l then 8/1000 else δ

def smallUpper (p : Profile) (l : ℝ) : ℝ :=
  if p = .coarse then 2/100 else if l ≤ 6/1000 then 6/1000 else
    if δ ≤ l ∧ l ≤ 8/1000 then 8/1000 else 2/100

def cone (p : Profile) (l : ℝ) : ℝ :=
  if l ≤ 2/100 then min (365/100000) (smallLower p l/2)
  else min (36/10000) (sSup {b : ℝ | b ∈ mediumBreaks ∧ b < l}/2-w)

def orientation (X D : Finset Plane) (v u : Plane) : Prop :=
  v ∈ X ∧ u ∈ D ∧ u ∈ X ∧ u ≠ v ∧ ∃ p ∈ X, ∃ q ∈ X, consecutive X u p q ∧ consecutive X v p q

def minorArc (X : Finset Plane) (u v : Plane) : Prop :=
  ∃ p ∈ X, ∃ q ∈ X, consecutive X u p q ∧ consecutive X v p q ∧
    ∀ z ∈ X, ¬ inMinorInterior p q u v z

def arcLength (X : Finset Plane) (u v : Plane) : ℝ := by
  classical exact if minorArc X u v then 2*Real.arcsin (chord u v/2)
    else 2*Real.pi-2*Real.arcsin (chord u v/2)

/-- Signed offset from the upward vertical, under rotation θ. -/
def aligned (θ t : ℝ) (v u : Plane) : Prop :=
  Placement.rotate θ (u-v) = dist u v • Wave.point (-Real.sin t) (Real.cos t)

def candidate (X D : Finset Plane) (p : Profile) (θ : ℝ) (v u : Plane) : Prop :=
  orientation X D v u ∧ minorArc X u v ∧ chord u v ∈ Icc δR (245/1000) ∧
    ∃ t, |t| ≤ cone p (chord u v) ∧ aligned θ t v u

def unitCandidate (θ : ℝ) (x y : Plane) : Prop :=
  ∃ t : ℝ, |t| ≤ w ∧ Placement.rotate θ (y-x) = Wave.point (Real.sin t) (Real.cos t)

end
end HadwigerNelson.Centres
