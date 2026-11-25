import ZetaSixth

/-!
# Statements for the certificate and assembly proofs

This file records the proof obligations as propositions and checks their proofs. It can be checked
independently with `lake env lean Blueprint.lean`.
-/

namespace ZetaSixth.Blueprint

open Filter MeasureTheory

def localFactor_closedForm : Prop :=
  ∀ p : Nat.Primes,
    let q : ℝ := (p : ℕ)
    localFactor p = (1 - q⁻¹) ^ 4 * (1 + 4 / q + 1 / q ^ 2)

def a3_multipliable : Prop := Multipliable (fun p : Nat.Primes => localFactor p)
def a3_pos : Prop := 0 < a3

def J_involutive : Prop := Function.Involutive J
def J_mem_Ω : Prop := ∀ p ∈ Ω, J p ∈ Ω
def J_measurePreserving : Prop := MeasurePreserving J chamberVolume chamberVolume
def v_comp_J : Prop := ∀ p, v (J p) = v p
def J_U7 : Prop := J '' U7 = U7
def J_ceiling : Prop := J '' ceiling = ceiling
def U7_subset_ceiling : Prop := U7 ⊆ ceiling
def mu_finite : Prop := μ Set.univ < ⊤

def mu_Omega : Prop := μ Ω = 42
def mu_U7 : Prop := μ U7 = ENNReal.ofReal (C : ℝ)
def mu_ceiling : Prop := μ ceiling = ENNReal.ofReal (ceilingMass : ℝ)

def U7_complement_ae : Prop :=
  let loss := N0 \ (balanced ∪ FPlus)
  (Ω \ U7 : Set Point) =ᵐ[volume] (loss ∪ J '' loss : Set Point)

def mu_U7_from_loss : Prop :=
  μ U7 = 42 - 2 * μ (N0 \ (balanced ∪ FPlus))

def mu_N0 : Prop := μ N0 = ENNReal.ofReal (209 / 1024 : ℝ)

/-- The complement of the first three components and their reflections in §10. -/
noncomputable def ceilingLoss : Set Point :=
  Ω ∩ {p | 1 < trace p ∧ trace p < 2 ∧ 1 / 4 < p.1 ∧ p.2.2 < 3 / 4 ∧
    p.2.2 < shortSum p ∧ p.2.1 + p.2.2 - p.1 < 1}

def ceiling_complement_ae : Prop :=
  (Ω \ (ceilingBase ∪ J '' ceilingBase) : Set Point) =ᵐ[volume] ceilingLoss

def mu_ceiling_reduction : Prop :=
  μ ceiling = 42 - μ ceilingLoss +
    2 * μ (ceilingLoss ∩ balanced) + 2 * μ ((ceilingLoss ∩ FPlus) \ balanced)

/-- Proposition 8, with projection of the (L^2) class of (v). -/
def projection_principle : Prop :=
  ∀ (𝒯 : Family), Faithful 𝒯 → ∀ (h : Profile), (h : Point → ℝ) =ᵐ[chamberVolume] v →
    ∀ c : ℝ, c < (Nat.factorial 9 : ℝ) * ‖(familySpan 𝒯).starProjection h‖ ^ 2 →
      ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T

/-- The indicator form of Proposition 8 used in §9. -/
def bound_of_indicator : Prop :=
  ∀ (𝒯 : Family) (U : Set Point), Faithful 𝒯 → MeasurableSet U → U ⊆ Ω →
    InFamilySpan 𝒯 (U.indicator v) →
    ∀ c : ℝ, c < (μ U).toReal →
      ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T

/-- The projection ceiling of Proposition 3 for profiles vanishing off the support union. -/
def projection_ceiling : Prop :=
  ∀ (𝒯 : Family) (h : Profile), (h : Point → ℝ) =ᵐ[chamberVolume] v →
    (∀ (B : Test) (g : Profile), (B, g) ∈ 𝒯 →
      ∀ᵐ p ∂chamberVolume, p ∉ ceiling → g p = 0) →
    (Nat.factorial 9 : ℝ) * ‖(familySpan 𝒯).starProjection h‖ ^ 2 ≤ (μ ceiling).toReal

def main_of : Prop := ConditionalMain

def lemma90 : Prop := Exponents.Lemma90
def lemma90_covering : Prop := Exponents.Covering


example : localFactor_closedForm := ZetaSixth.localFactor_closedForm
example : a3_multipliable := ZetaSixth.a3_multipliable
example : a3_pos := ZetaSixth.a3_pos
example : J_involutive := ZetaSixth.J_involutive
example : J_mem_Ω := fun _ h => ZetaSixth.J_mem_Ω h
example : J_measurePreserving := ZetaSixth.J_measurePreserving
example : v_comp_J := ZetaSixth.v_comp_J
example : J_U7 := ZetaSixth.J_U7
example : J_ceiling := ZetaSixth.J_ceiling
example : U7_subset_ceiling := ZetaSixth.U7_subset_ceiling
example : mu_finite := ZetaSixth.mu_finite
example : mu_Omega := ZetaSixth.mu_Omega
example : mu_U7 := ZetaSixth.mu_U7
example : mu_ceiling := ZetaSixth.mu_ceiling
example : U7_complement_ae := ZetaSixth.U7_complement_ae

example : mu_U7_from_loss := by
  simpa only [ZetaSixth.mu_Omega] using ZetaSixth.mu_U7_from_loss

example : mu_N0 := ZetaSixth.mu_N0
example : ceiling_complement_ae := ZetaSixth.ceiling_complement_ae

example : mu_ceiling_reduction := by
  simpa only [ZetaSixth.mu_Omega] using ZetaSixth.mu_ceiling_reduction

example : projection_principle := ZetaSixth.projection_principle
example : bound_of_indicator := ZetaSixth.bound_of_indicator
example : projection_ceiling := ZetaSixth.projection_ceiling
example : main_of := ZetaSixth.main_of
example : lemma90 := ZetaSixth.Exponents.lemma90
example : lemma90_covering := ZetaSixth.Exponents.lemma90_covering

end ZetaSixth.Blueprint
