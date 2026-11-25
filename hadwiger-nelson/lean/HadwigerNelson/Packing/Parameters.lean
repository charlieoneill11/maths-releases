import HadwigerNelson.Plane
import Mathlib.Data.Nat.Lattice

namespace HadwigerNelson.Packing
noncomputable section

def separated (P : Finset Plane) (δ : ℝ) : Prop := ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ < dist x y

def nearDegree (P : Finset Plane) (z : Plane) (t : ℝ) : ℕ := by
  classical exact (P.filter fun y => y ≠ z ∧ dist y z ≤ 2 * t).card

def annulusCosine (a b : ℝ) : ℝ :=
  max ((2*a^2-1)/(2*a^2)) (max ((a^2+b^2-1)/(2*a*b)) ((2*b^2-1)/(2*b^2)))

def annulusCap (a b : ℝ) (fallback : ℕ) : ℕ := by
  classical
  let test := fun k : ℕ =>
    let ψ := (44 : ℝ) / (7 * (k + 1 : ℕ))
    4 ≤ k ∧ k ≤ 127 ∧ annulusCosine a b < 1 - ψ^2/2 + ψ^4/24 - ψ^6/720
  exact if h : ∃ k, test k then Nat.find h else fallback

/-- Lemma 31, with the disk-area bound as a finite fallback when an angular
test fails. The outer minimum makes this equivalent to an infinite fallback. -/
def neighbourCap (ρ t : ℝ) : ℕ := by
  classical
  let A := ⌊(1 + 2*t/ρ)^2⌋₊ - 1
  let M := ⌈100*t/ρ⌉₊
  exact if t ≤ ρ then 0 else sInf {b : ℕ | b = A ∨ b = annulusCap 1 (M/100 : ℝ) A ∨
    ∃ j : ℕ, 11 ≤ j ∧ 10*j < M ∧ b =
      annulusCap 1 (j/10 : ℝ) A + annulusCap (j/10 : ℝ) (M/100 : ℝ) A}

def shortPairs (X : Finset Plane) (δ : ℝ) : ℕ := by
  classical exact (∑ x ∈ X, (X.filter fun y => x ≠ y ∧ dist x y < δ).card) / 2

end
end HadwigerNelson.Packing
