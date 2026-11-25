import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Public statements and definitions for the least-prime and divisor-density theorems. -/

namespace LeastPrime

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- The natural numbers in `(Q/2, Q]` for `Q ≥ 0`. -/
def window (Q : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊Q⌋₊ + 1)).filter (fun n => Q / 2 < (n : ℝ))

/-- Every reduced residue class modulo `n` contains a prime at most `B`. -/
def AllClassesBelow (n : ℕ) (B : ℝ) : Prop :=
  ∀ a : ℕ, Nat.Coprime a n → ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD n] ∧ (p : ℝ) ≤ B

/-- `n` has a divisor `d` with `n ^ α ≤ d ≤ n ^ β`. -/
def HasDivisorIn (n : ℕ) (α β : ℝ) : Prop :=
  ∃ d ∈ n.divisors, (n : ℝ) ^ α ≤ d ∧ (d : ℝ) ≤ (n : ℝ) ^ β

/-- The density assertion in Theorem 1 for given constants. -/
def mainBound (C δ : ℝ) : Prop := by
  classical
  exact ∀ᶠ Q in atTop,
    (0.587 : ℝ) * (window Q).card <
      ((window Q).filter (fun n => AllClassesBelow n (C * (n : ℝ) ^ (2 - δ)))).card

/-- Theorem 1. The paper gives the witness `C = 4`. -/
def main : Prop := ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ mainBound C δ

/-- Theorem 2(1). -/
def density_lower : Prop := by
  classical
  exact ∀ᶠ Q in atTop,
    (0.5871 : ℝ) * (window Q).card <
      ((window Q).filter (fun n => HasDivisorIn n 0.142858 0.199999)).card

/-- Theorem 2(2). -/
def density_upper : Prop := by
  classical
  exact ∀ᶠ Q in atTop,
    (((window Q).filter (fun n => HasDivisorIn n (1 / 7) (1 / 5))).card : ℝ) <
      0.5956 * (window Q).card

/-- Stick-breaking on the unit cube. -/
def stick (j : ℕ) (u : Fin j → ℝ) : Fin j → ℝ :=
  fun i => u i * ∏ k ∈ Finset.univ.filter (· < i), (1 - u k)

/-- The law of the first `j` stick lengths. -/
def stickLaw (j : ℕ) : Measure (Fin j → ℝ) :=
  (volume.restrict (univ.pi fun _ => Icc (0 : ℝ) 1)).map (stick j)

/-- The simplex of nonnegative pieces with total length at most one. -/
def simplex (j : ℕ) : Set (Fin j → ℝ) :=
  {v | (∀ i, v i ∈ Icc (0 : ℝ) 1) ∧ ∑ i, v i ≤ 1}

/-- The remaining length after revealing the first pieces. -/
def remainder {j : ℕ} (v : Fin j → ℝ) : ℝ := 1 - ∑ i, v i

/-- The event that a subset sum, with or without the full remainder, meets `T`. -/
def E (j : ℕ) (T : Set ℝ) : Set (Fin j → ℝ) :=
  {v | v ∈ simplex j ∧ ∃ S : Finset (Fin j), ∃ ε : ℝ,
    (ε = 0 ∨ ε = 1) ∧ (∑ i ∈ S, v i) + ε * remainder v ∈ T}

/-- The event that a subset sum plus some portion of the remainder meets `T`. -/
def F (j : ℕ) (T : Set ℝ) : Set (Fin j → ℝ) :=
  {v | v ∈ simplex j ∧ ∃ S : Finset (Fin j), ∃ y ∈ Icc 0 (remainder v),
    (∑ i ∈ S, v i) + y ∈ T}

def Tin : Set ℝ := Icc 0.142858 0.199999 ∪ Icc 0.800001 0.857142

/-- The outward-rounded symmetric interval union from Proposition 14. -/
def Tout : Set ℝ := Icc 0.142857 0.2 ∪ Icc 0.8 0.857143

/-- The lower bound in Proposition 14. -/
def P6Tin : Prop := 0.587142 ≤ (stickLaw 6).real (E 6 Tin)

/-- The upper bound in Proposition 14. -/
def Q5Tout : Prop := (stickLaw 5).real (F 5 Tout) ≤ 0.595573

theorem window_eq_Ioc {Q : ℝ} (hQ : 0 ≤ Q) : window Q = Finset.Ioc ⌊Q / 2⌋₊ ⌊Q⌋₊ := by
  classical
  ext n
  have hhalf : 0 ≤ Q / 2 := by positivity
  simp only [window, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff]
  rw [← Nat.floor_lt hhalf, and_comm]

theorem window_card {Q : ℝ} (hQ : 0 ≤ Q) :
    (window Q).card = ⌊Q⌋₊ - ⌊Q / 2⌋₊ := by
  rw [window_eq_Ioc hQ, Nat.card_Ioc]

theorem not_allClassesBelow_three_one : ¬ AllClassesBelow 3 1 := by
  intro h
  obtain ⟨p, hp, _, hbound⟩ := h 1 (by decide)
  exact (not_le_of_gt (show 1 < (p : ℝ) by exact_mod_cast hp.one_lt)) hbound

theorem measurable_stick (j : ℕ) : Measurable (stick j) := by
  unfold stick
  fun_prop

instance instIsProbabilityMeasureStickLaw (j : ℕ) : IsProbabilityMeasure (stickLaw j) where
  measure_univ := by
    rw [stickLaw, Measure.map_apply (measurable_stick j) MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, volume_pi_pi]
    simp [Real.volume_Icc]

/-- The only coordinate of `stickLaw 1` is uniform on the unit interval. -/
theorem stickLaw_one : (stickLaw 1).map (fun u => u 0) =
    volume.restrict (Icc (0 : ℝ) 1) := by
  have hstick : stick 1 = id := by
    funext u i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [stick]
  let coord : (Fin 1 → ℝ) → ℝ := fun u => u 0
  have hcoord : MeasurePreserving coord := volume_preserving_funUnique (Fin 1) ℝ
  have hcube : (univ.pi fun _ : Fin 1 => Icc (0 : ℝ) 1) = coord ⁻¹' Icc 0 1 := by
    ext u
    simp only [Set.mem_pi, mem_univ, true_implies, mem_preimage, coord]
    exact ⟨fun h => h 0, fun h i => (Subsingleton.elim (0 : Fin 1) i) ▸ h⟩
  change (stickLaw 1).map coord = _
  rw [stickLaw, hstick, Measure.map_id, hcube]
  ext s hs
  rw [Measure.map_apply hcoord.measurable hs, Measure.restrict_apply (hcoord.measurable hs),
    Measure.restrict_apply hs, ← preimage_inter]
  exact hcoord.measure_preimage (hs.inter measurableSet_Icc).nullMeasurableSet

theorem E_subset_F (j : ℕ) (T : Set ℝ) : E j T ⊆ F j T := by
  rintro v ⟨hv, S, ε, hε, hT⟩
  have hr : 0 ≤ remainder v := sub_nonneg.mpr hv.2
  refine ⟨hv, S, ε * remainder v, ?_, hT⟩
  rcases hε with rfl | rfl
  · simpa using hr
  · simpa using hr

theorem stickLaw_one_real_E : (stickLaw 1).real (E 1 (Icc 0.4 0.6)) = 0.2 := by
  let coord : (Fin 1 → ℝ) → ℝ := fun v => v 0
  have hcoord : Measurable coord := measurable_pi_apply 0
  have hE : E 1 (Icc 0.4 0.6) = coord ⁻¹' Icc 0.4 0.6 := by
    ext v
    have hr : remainder v = 1 - v 0 := by simp [remainder]
    change (_ ∧ _) ↔ v 0 ∈ Icc (0.4 : ℝ) 0.6
    constructor
    · rintro ⟨_, S, ε, hε, hmem⟩
      have hS : S = ∅ ∨ S = {0} := by
        by_cases h : (0 : Fin 1) ∈ S
        · right
          ext i
          have hi : i = 0 := Subsingleton.elim _ _
          simpa [hi] using h
        · left
          ext i
          have hi : i = 0 := Subsingleton.elim _ _
          simpa [hi] using h
      rcases hS with rfl | rfl <;> rcases hε with rfl | rfl
      · norm_num [mem_Icc] at hmem
      · simp only [Finset.sum_empty, zero_add, one_mul, hr, mem_Icc] at hmem
        exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
      · simpa using hmem
      · simp only [Finset.sum_singleton, one_mul, hr, mem_Icc] at hmem
        exfalso
        linarith [hmem.2]
    · intro hv
      refine ⟨⟨?_, ?_⟩, {0}, 0, Or.inl rfl, by simpa using hv⟩
      · intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
      · rw [Fin.sum_univ_one]
        linarith [hv.2]
  rw [hE, measureReal_def, ← Measure.map_apply hcoord measurableSet_Icc, stickLaw_one]
  have hsubset : Icc (0.4 : ℝ) 0.6 ⊆ Icc 0 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hsubset]
  change volume.real (Icc (0.4 : ℝ) 0.6) = _
  rw [Real.volume_real_Icc]
  norm_num

end

end LeastPrime
