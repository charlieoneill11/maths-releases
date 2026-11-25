import ZetaSixth.Statement
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity

namespace ZetaSixth

open MeasureTheory

abbrev Point := ℝ × ℝ × ℝ

/-- The ordered chamber from §2.1. -/
def Ω : Set Point := {p | 0 < p.1 ∧ p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.2.2 < 1}

/-- The Weyl dimension polynomial from §2.1. -/
noncomputable def v (p : Point) : ℝ :=
  (p.2.2 - p.2.1) * (p.2.2 - p.1) * (p.2.1 - p.1) / 2

/-- Reflection of the chamber from §2.1. -/
noncomputable def J (p : Point) : Point := (1 - p.2.2, 1 - p.2.1, 1 - p.1)

noncomputable def chamberVolume : Measure Point := volume.restrict Ω

/-- The measure (9! v^2,dx,dy,dz) on the chamber from §2.1. -/
noncomputable def μ : Measure Point :=
  chamberVolume.withDensity (fun p => ENNReal.ofReal ((Nat.factorial 9 : ℝ) * v p ^ 2))

/-- The sum of the two smaller coordinates, denoted (k) in §2.1. -/
noncomputable def shortSum (p : Point) : ℝ := p.1 + p.2.1

/-- The trace (r) in §2.1. -/
noncomputable def trace (p : Point) : ℝ := shortSum p + p.2.2

/-- The part of the chamber accessible to the unequal-length tests, §4. -/
noncomputable def Dacc : Set Point :=
  Ω ∩ {p | 3 * min p.1 (1 - p.2.2) + 5 * max p.1 (1 - p.2.2) < 2 ∨
    shortSum p < 1 / 2 ∨ 3 / 2 < p.2.1 + p.2.2}

/-- The low and high trace regions, §4. -/
noncomputable def A : Set Point := Ω ∩ {p | trace p < 1 ∨ 2 < trace p}

/-- The support of Theorem 16. -/
noncomputable def S3 : Set Point := Dacc ∪ A

/-- The marked region of §5. -/
noncomputable def marked : Set Point := Ω ∩ {p | 1 / 2 < p.2.2 - p.1}

/-- The low-trace half of the complement in Theorem 23, up to null sets. -/
noncomputable def N0 : Set Point :=
  Ω ∩ {p | 1 < trace p ∧ trace p < 3 / 2 ∧ 1 / 2 < shortSum p ∧ p.2.2 - p.1 < 1 / 2}

/-- The balanced-row support of §6. -/
noncomputable def balanced : Set Point :=
  Ω ∩ {p | 1 < trace p ∧ trace p < 15 / 14 ∧ 21 * shortSum p + 7 * trace p < 18}

/-- The four caps in equation (48) of §8, on the domain (1/2<k<3/5). -/
noncomputable def xPlus (k : ℝ) : ℝ :=
  if k < 10 / 19 then k / 2
  else if k < 7 / 13 then max ((21 - 39 * k) / 2) ((7 - 12 * k) / 4)
  else if k < 4 / 7 then (2 - 3 * k) / 4
  else (3 - 5 * k) / 2

/-- The mark region (mathcal P^+) of §8. -/
noncomputable def PPlus : Set (ℝ × ℝ) :=
  {a | 0 < a.1 ∧ a.1 < 1 ∧ 0 < a.2 ∧ a.2 < 1 ∧
    1 / 2 < a.1 + a.2 ∧ a.1 + a.2 < 3 / 5 ∧ a.1 < xPlus (a.1 + a.2)}

/-- The mixed-row support (mathcal F^+) of §8. -/
noncomputable def FPlus : Set Point :=
  Ω ∩ {p | 1 < trace p ∧ trace p < 3 / 2 ∧ (p.1, p.2.1) ∈ PPlus}

/-- The support of Theorem 79. -/
noncomputable def U7 : Set Point :=
  S3 ∪ marked ∪ balanced ∪ J '' balanced ∪ FPlus ∪ J '' FPlus

/-- The dominant, low-trace and small-coordinate supports listed in §10. -/
noncomputable def ceilingBase : Set Point :=
  Ω ∩ {p | shortSum p < p.2.2 ∨ trace p < 1 ∨ p.1 < 1 / 4}

/-- The support union (mathcal U) of Proposition 3 and §10. -/
noncomputable def ceiling : Set Point :=
  ceilingBase ∪ J '' ceilingBase ∪ balanced ∪ J '' balanced ∪ FPlus ∪ J '' FPlus

/-- The exact ceiling in Proposition 3. -/
def ceilingMass : ℚ := 13860404849860091 / 330432202525696

/-- The exact masses from Theorems 16, 23, 52 and 67 recorded in the §9 table. -/
def intermediateMasses : List ℚ :=
  [8263261393 / 200000000, 42 - 209 / 512, 2578241177999 / 61983140352,
    3307268442615739142376085993 / 79479266349492187500000000]

theorem ceilingMass_lt : ceilingMass < 42 := by norm_num [ceilingMass]

end ZetaSixth
