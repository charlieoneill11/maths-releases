import HadwigerNelson.Centres.Events.Definitions
import HadwigerNelson.Blueprint.Point.Budgets
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace HadwigerNelson.Forest
open MeasureTheory Set
open scoped BigOperators
open Centres Crossings
noncomputable section
attribute [local instance] Classical.propDecidable
local notation "Ωfn" => (ℝ → ℝ → ℝ)

def a : ℝ := δR/2
def d : ℝ := δ/2
def unitBin (k : ℕ) : ℝ := k*w/16384
def shortBin (i : ℕ) : ℝ := (i:ℝ)/8192

def unitStep (Ω : Ωfn) : ℕ → ℝ
  | 0 => 1
  | k+1 => min (unitStep Ω k) (Ω (unitBin (k+1)) ((unitBin (k+1))^2/2))

def unitCredit (Ω : Ωfn) (t : ℝ) : ℝ := unitStep Ω (min 16384 (max 1 ⌈|t|/unitBin 1⌉₊))

def lowerShort (Ω : Ωfn) (ρ : ℝ) (i : ℕ) : ℝ :=
  let l := shortBin i
  let u := shortBin (i+1)
  Ω (2*ρ*(1-l^2)/(1+l^2)) (2*ρ*2*u/(1+u^2))

def shortIndex (v : Plane) : ℕ := min 8191 ⌊8192*|v 1|/(‖v‖+|v 0|)⌋₊

def cap (Ω : Ωfn) (ρ : ℝ) : ℝ :=
  (if ρ = a then 3/4 else 3/10 : ℝ) * sSup (Set.range (fun i : Fin 8192 => lowerShort Ω ρ i))

def cappedShort (Ω : Ωfn) (ρ : ℝ) (i : ℕ) : ℝ := min (lowerShort Ω ρ i) (cap Ω ρ)

structure Layers (X : Finset Plane) where
  R : Finset Plane
  D : Finset Plane
  maximalR : maximalSeparated X R δR
  maximalD : maximalSeparated R D δ
  parent : Plane → Plane
  outer : ∀ x ∈ X, x ∉ R → parent x ∈ R ∧ dist x (parent x) ≤ δR
  inner : ∀ x ∈ R, x ∉ D → parent x ∈ D ∧ dist x (parent x) ≤ δ
  fixed : ∀ x ∈ D, parent x = x

inductive Mode | r | d | centresOnly deriving DecidableEq

def eligible {X : Finset Plane} (L : Layers X) : Mode → Finset Plane
  | .r => L.R | .d => L.D | .centresOnly => ∅

def ordinary {X : Finset Plane} (L : Layers X) (m : Mode) (θ : ℝ) (x y : Plane) : Prop :=
  m ≠ .centresOnly ∧ ((y ∉ L.D ∧ L.parent y = x) ∨ (x ∈ eligible L m ∧ unitCandidate θ x y))

def allCandidates {X : Finset Plane} (L : Layers X) (m : Mode) (p : Profile) (θ : ℝ)
    (x y : Plane) : Prop := ordinary L m θ x y ∨ candidate X L.D p θ x y

def depth {X : Finset Plane} (L : Layers X) (x : Plane) : ℕ := by
  classical exact if x ∈ L.D then 0 else if L.parent x ∈ L.D then 1 else 2

def rootHeight {X : Finset Plane} (L : Layers X) (θ : ℝ) (x : Plane) : ℝ :=
  Placement.rotate θ (L.parent (L.parent x)) 1

def edgeShort {X : Finset Plane} (L : Layers X) (Ω : Ωfn) (m : Mode) (θ : ℝ) (y : Plane) : ℝ := by
  classical exact if m = .centresOnly ∨ y ∈ L.D then 0 else
    cappedShort Ω (if y ∈ L.R then d else a) (shortIndex (Placement.rotate θ (y-L.parent y)))

def headCap {X : Finset Plane} (L : Layers X) (Ω : Ωfn) (y : Plane) : ℝ := by
  classical exact if y ∈ L.D then 0 else if y ∈ L.R then cap Ω d else cap Ω a

def edgeUnit (Ω : Ωfn) (θ : ℝ) (x y : Plane) : ℝ := by
  classical exact if unitCandidate θ x y then unitCredit Ω (Real.arcsin ((Placement.rotate θ (y-x)) 0)) else 0
  -- The signed offset of a candidate is uniquely recovered in [-w,w].

def collisionLoss {X : Finset Plane} (L : Layers X) (Ω : Ωfn) (m : Mode) (θ : ℝ) (y : Plane) : ℝ := by
  classical exact (∑ u ∈ eligible L m, ∑ v ∈ eligible L m,
    if u ≠ v ∧ ¬(u ∈ L.D ∧ v ∈ L.D) then min (edgeUnit Ω θ u y) (edgeUnit Ω θ v y) else 0)/2

def excessCredit {X : Finset Plane} (L : Layers X) (Ω : Ωfn) (m : Mode) (θ : ℝ) (y : Plane) : ℝ :=
  ∑ x ∈ eligible L m, max (edgeUnit Ω θ x y - headCap L Ω y) 0

def shortMean (Ω : Ωfn) (ρ : ℝ) : ℝ :=
  2/Real.pi * ∑ i : Fin 8192, cappedShort Ω ρ i *
    (2*Real.arctan (shortBin (i.val+1))-2*Real.arctan (shortBin i.val))

def lowerShortMean (Ω : Ωfn) (ρ : ℝ) : ℝ :=
  2/(355/113:ℝ) * ∑ i : Fin 8192, cappedShort Ω ρ i *
    (2*(shortBin (i.val+1)-shortBin i.val)/(1+shortBin (i.val+1)^2))

def unitMean (Ω : Ωfn) : ℝ := 2*unitBin 1/Real.pi * ∑ k : Fin 16384, unitStep Ω (k.val+1)
def retention (Ω : Ωfn) (M : ℝ) : ℝ :=
  (∑ k : Fin 16384, max (unitStep Ω (k.val+1)-M) 0) / (∑ k : Fin 16384, unitStep Ω (k.val+1))

def neighbourPairs (R D : Finset Plane) (t : ℝ) : ℕ := by
  classical exact (∑ u ∈ R, (R.filter fun v =>
    u ≠ v ∧ ¬(u ∈ D ∧ v ∈ D) ∧ dist u v ≤ 2*t).card)/2

def packingSum (Ω : Ωfn) (takeBin : ℝ → Prop) : ℝ := by
  classical exact unitBin 1 / Real.pi * ∑ k : Fin 16384, let t := unitBin (k.val+1)
    if takeBin t then Packing.neighbourCap a t * unitStep Ω (k.val+1) else 0


end
end HadwigerNelson.Forest
