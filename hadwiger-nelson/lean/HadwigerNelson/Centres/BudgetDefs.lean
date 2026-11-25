import HadwigerNelson.Centres.Parameters
import HadwigerNelson.Blueprint.Point.Budgets

namespace HadwigerNelson.Centres
open Crossings
noncomputable section

def shortArcCount (X : Finset Plane) (radius : ℝ) : ℕ := by
  classical exact (∑ u ∈ X, ∑ p ∈ X,
    (X.filter fun q => consecutive X u p q ∧ dist p q < radius).card) / 2

def shortDoubledCount (X : Finset Plane) (radius : ℝ) : ℕ := by
  classical exact (∑ p ∈ X, (X.filter fun q => dist p q < radius ∧
    ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ consecutive X u p q ∧ consecutive X v p q).card)/2

def admissible (X : Finset Plane) (radius b : ℝ) : Prop :=
  0 ≤ b ∧ shortDoubledCount X radius ≤ b ∧ shortArcCount X radius ≤ 2*b

def outsideDegree (X R : Finset Plane) : ℕ := by
  classical exact ∑ x ∈ X \ R, unitDegree X x

def orientationSet (X D : Finset Plane) (r : ℝ) : Finset (Plane × Plane) := by
  classical exact (X ×ˢ D).filter fun z => orientation X D z.1 z.2 ∧ r ≤ chord z.2 z.1

def angularBudget (n m t h : ℕ) (LD bR bD : ℝ) : ℝ :=
  let Q := Real.pi*n - ((m:ℝ)-bR)*δR - ((m:ℝ)-bD)*(δ-δR)
  let QD := Q - Real.pi*h + δ*LD/2
  let singles := fun i : Fin 7 =>
    let K := diskLimit i
    let B : ℝ := ((K-1)*(n-h)/2 : ℕ) + min (2*LD) (K*h+h.choose 2 : ℕ)
    2*(m:ℝ)-2*t-B
  min (Q - (∑ i, excessWidth i * max (singles i) 0)/2)
    (QD - (∑ i, excessWidth i * max (singles i - LD) 0)/2)

end
end HadwigerNelson.Centres
