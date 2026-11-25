import HadwigerNelson.Crossings.Doubled
import HadwigerNelson.Blueprint.Point.Rhombus

namespace HadwigerNelson

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Forest

/-- Lemma 37 compares the short credit to all unit credits at a single head. -/
theorem max_sum_lower {r : ℕ} (h : Fin r → ℝ) (c M ε : ℝ) (hc : 0 ≤ c)
    (hM : c ≤ M) (hh : ∀ i, 0 ≤ h i) (hε : 0 ≤ ε) :
    c + (∑ i, max (h i - M) 0) - ε ≤ max c ((∑ i, h i) - ε) := by
  by_cases H : ∃ i, M < h i
  · obtain ⟨i, hi⟩ := H
    have cap : M ≤ ∑ j, min (h j) M := by
      have hi' := Finset.single_le_sum (s := Finset.univ) (f := fun j => min (h j) M)
        (fun j _ => le_min (hh j) (hc.trans hM)) (Finset.mem_univ i)
      simpa [min_eq_right hi.le] using hi'
    have split (j : Fin r) : min (h j) M + max (h j - M) 0 = h j := by
      rcases le_total (h j) M with h₁ | h₂
      · simp [min_eq_left h₁, max_eq_right (sub_nonpos.mpr h₁)]
      · rw [min_eq_right h₂, max_eq_left (sub_nonneg.mpr h₂)]
        ring
    apply le_max_of_le_right
    calc
      _ ≤ (∑ j, (min (h j) M + max (h j - M) 0)) - ε := by
        rw [Finset.sum_add_distrib]
        linarith
      _ = _ := by simp_rw [split]
  · have hle (i : Fin r) := le_of_not_gt (fun hgt => H ⟨i, hgt⟩)
    apply le_max_of_le_left
    simp [fun i => max_eq_right (sub_nonpos.mpr (hle i)), hε]

end Forest

namespace Centres

open Crossings

theorem doubled_pairs_lower (facts : CitedFacts) (X : Finset Plane)
    (hn : 1317 ≤ X.card) (hd : minNonisolatedDegree X 3) :
    2 * (unitEdgeCount X : ℤ) - retainedArcBound X.card (unitEdgeCount X) ≤ doubledPairs X := by
  exact doubled_pairs_lower_bound facts X hn hd

/-- The seven chord thresholds in Lemma 51, in tenths of δ. -/
def tenths (i : Fin 7) : ℕ := 14 + 5*i.val

def diskLimit (i : Fin 7) : ℕ := (10 + 2*tenths i)^2 / 100

def excessWidth (i : Fin 7) : ℝ :=
  (if i.val = 0 then 4 else 5 : ℝ) / 10 * (1837/250000)

/-- The lower bound for doubled pairs substituted into Proposition 52 may be negative. -/
def pairLower (n m : ℕ) : ℝ := 2*(m : ℝ) - (retainedArcBound n m : ℝ)

/-- The two tiers of the angle budget, after evaluating the bounds of Lemmas
45, 50 and 51. The factor 355/113 bounds π from above on each set of circles. -/
def profileCredit (n m s j : ℕ) (I IR J : ℝ) : ℝ :=
  let h := s + j
  let LD := weightedBound n m h 0 1 0
  let LR := weightedBound n m s 0 1 0
  let bR := min LR (min (5*s + s.choose 2 : ℕ) ((LR + 5*s)/2))
  let bD := min LD (min (14*s + 8*j + s.choose 2 : ℕ) ((LD + 5*h)/2))
  let t := pairLower n m
  let xR := t - bR - LD/2
  let xD := t - bD - LD/2
  let δR : ℝ := 53/10000
  let δ : ℝ := 1837/250000
  let reserve := (m - bR : ℝ)*δR + (m - bD : ℝ)*(δ-δR)
  let Q := (355/113 : ℝ)*n - reserve
  let QD := (355/113 : ℝ)*(n-h : ℕ) - reserve + δ*LD/2
  let singles := fun i : Fin 7 =>
    let K := diskLimit i
    let budget : ℝ := ((K-1)*(n-h)/2 : ℕ) + min (2*LD) (K*h + h.choose 2 : ℕ)
    2*(m : ℝ) - 2*t - budget
  let Qstar := min (Q - (∑ i, excessWidth i * max (singles i) 0)/2)
    (QD - (∑ i, excessWidth i * max (singles i - LD) 0)/2)
  max 0 (max (IR * max xR 0 + (I-IR)*max xD 0 - J*min Q QD)
    (IR*xR + (I-IR)*xD - J*Qstar))

def centreCredit (n m s j : ℕ) : ℝ :=
  max (profileCredit n m s j (230/10^10) (79/10^10) (980/10^10))
    (profileCredit n m s j (259/10^10) (93/10^10) (1100/10^10))

end Centres

namespace Certificate

/-- Section 9 objective with the two collision constants computed from the
pointwise packing bound in Lemma 31. All entries in this definition are in
units of 10⁻¹⁸ until the final division. -/
def pointObjective (n m s j : ℕ) : ℝ :=
  let q : ℝ := 71152801254159
  let p : ℝ := 708385488148
  let B : ℝ := 112668096940
  let C : ℝ := 16034576942481
  let E : ℝ := 3057937052494
  let L : ℝ := 150296106235
  let T : ℝ := 97911102803
  let U : ℝ := 104770006866
  let J : ℝ := 300592212470
  let base := n*q + m*(p-B) - s*C - j*E
  let rCost := min ((n-s : ℕ)*L) (min ((n-s : ℕ)*T + j*U) (j*J))
  let modeR := base + B*Crossings.weightedBound n m s j (828/1000) (1195/10000) + rCost
  let modeD := base + B*Crossings.weightedBound n m s j (828/1000) (6195/10000)
  min (n*q + m*p) (min modeR modeD) / 10^18 - Centres.centreCredit n m s j

end Certificate

namespace Forest

/-- In a finite set, a maximal separated subset is equivalently a separated
subset whose closed balls cover all omitted points. -/
def maximalSeparated (X P : Finset Plane) (δ : ℝ) : Prop :=
  P ⊆ X ∧ Packing.separated P δ ∧ ∀ x ∈ X, x ∉ P → ∃ y ∈ P, dist x y ≤ δ

end Forest

end
end HadwigerNelson
