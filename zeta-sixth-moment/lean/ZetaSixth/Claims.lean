import ZetaSixth.Regions
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space

namespace ZetaSixth

open Filter MeasureTheory
open scoped Topology

/-- A test from §2.4. Values at bounded heights do not affect the limits at infinity. -/
abbrev Test := ℝ → C(ℝ, ℂ)

/-- The nonnegative, nonzero smooth weights with compact support in (1, 2), §2.4. -/
structure Weight where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) toFun
  nonnegative : ∀ t, 0 ≤ toFun t
  compactSupport : HasCompactSupport toFun
  supportInside : tsupport toFun ⊆ Set.Ioo 1 2
  nonzero : ∃ t, toFun t ≠ 0

instance : CoeFun Weight (fun _ => ℝ → ℝ) := ⟨Weight.toFun⟩

/-- The time normalization in §2.4, equal to (9!c_3 T(log T)^9\intPhi). -/
noncomputable def timeNorm (Φ : Weight) (T : ℝ) : ℝ :=
  a3 * T * Real.log T ^ 9 * ∫ t, Φ t

/-- The target pairing in §2.4, with the test in the conjugated slot. -/
noncomputable def numerator (Φ : Weight) (B : Test) (T : ℝ) : ℂ :=
  ∫ t, (Φ (t / T) : ℂ) * zetaLine t ^ 3 * star (B T t)

/-- The Gram pairing in §2.4, with the second test in the conjugated slot. -/
noncomputable def gram (Φ : Weight) (B B' : Test) (T : ℝ) : ℂ :=
  ∫ t, (Φ (t / T) : ℂ) * B T t * star (B' T t)

/-- Real profiles in (L^2(Omega,dx,dy,dz)), using restricted volume. -/
noncomputable abbrev Profile := Lp ℝ 2 chamberVolume

/-- A family of tests paired with real profiles, Definition 7. -/
noncomputable abbrev Family := Set (Test × Profile)

/-- Both limits hold for each allowed weight and each pair of family members, Definition 7.
The integral expressions are the real (L^2) inner products with Lebesgue measure. -/
def Faithful (𝒯 : Family) : Prop :=
  (∀ (Φ : Weight) (B : Test) (h : Profile), (B, h) ∈ 𝒯 →
    Tendsto (fun T => numerator Φ B T / (timeNorm Φ T : ℂ)) atTop
      (𝓝 ((∫ p, v p * h p ∂chamberVolume : ℝ) : ℂ))) ∧
  (∀ (Φ : Weight) (B B' : Test) (h h' : Profile), (B, h) ∈ 𝒯 → (B', h') ∈ 𝒯 →
    Tendsto (fun T => gram Φ B B' T / (timeNorm Φ T : ℂ)) atTop
      (𝓝 ((inner ℝ h h' : ℝ) : ℂ)))

/-- The closed real linear span of the profiles of a family, Definition 7. -/
noncomputable abbrev familySpan (𝒯 : Family) : Submodule ℝ Profile :=
  (Submodule.span ℝ (Prod.snd '' 𝒯)).topologicalClosure

/-- Membership in the closed span of the (L^2) class represented by a function. -/
def InFamilySpan (𝒯 : Family) (f : Point → ℝ) : Prop :=
  ∃ h ∈ familySpan 𝒯, (h : Point → ℝ) =ᵐ[chamberVolume] f

/-- Theorem 79 of the paper, building on Theorems 16, 23, 52 and 67. The paper supplies
the analytic proof. This structure records its conclusion as a hypothesis.

Those theorems use Fraccaro's moment formulas, the Kuznetsov formula and spectral large
sieves, Kim–Sarnak, Deshouillers–Iwaniec on Kloosterman fractions with the Lichtman and
Drappeau corrections, Pascadi's exceptional spectrum estimate, Heath-Brown on (d_3)
in progressions, Fouvry–Kowalski–Michel, and Harper's sixth-moment bound, which rests
on RH. The four estimates in §8.1 (Deshouillers–Iwaniec Theorem 12, Lichtman Lemma 7.5,
Drappeau Theorem 2.1, and Pascadi Lemmas 3.9–3.10) remain unchecked against their
published statements. -/
structure PaperPairings : Prop where
  exists_faithful : ∃ 𝒯 : Family, Faithful 𝒯 ∧ InFamilySpan 𝒯 (U7.indicator v)

/-- The conditional version of Theorem 2 to be established in the assembly. -/
def ConditionalMain : Prop := PaperPairings → MainBound

end ZetaSixth
