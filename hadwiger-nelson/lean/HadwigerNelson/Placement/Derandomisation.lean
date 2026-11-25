import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite-edge derandomisation for the random placements in §2.2 and §4. -/

open MeasureTheory
open scoped BigOperators

namespace HadwigerNelson.Placement

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An integrable count of expectation below one vanishes at a placement in any full-measure
set. This allows the finitely many blank boundary events of the complete wave to be discarded. -/
theorem exists_zero_of_integral_lt_one (count : Ω → ℕ) (good : Ω → Prop)
    (hgood : ∀ᵐ ω ∂μ, good ω) (hint : Integrable (fun ω ↦ (count ω : ℝ)) μ)
    (hsmall : ∫ ω, (count ω : ℝ) ∂μ < 1) : ∃ ω, good ω ∧ count ω = 0 := by
  by_contra h
  have hpos : ∀ᵐ ω ∂μ, (1 : ℝ) ≤ count ω := by
    filter_upwards [hgood] with ω hω
    have hn : count ω ≠ 0 := fun hz ↦ h ⟨ω, hω, hz⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hle := integral_mono_ae (integrable_const (1 : ℝ)) hint hpos
  have hone : (1 : ℝ) ≤ ∫ ω, (count ω : ℝ) ∂μ := by simpa using hle
  exact (not_lt_of_ge hone) hsmall

/-- A finite family of events, each of probability at most `p`, is simultaneously avoided if
`card * p < 1`. The chosen placement can also satisfy an almost-sure condition. -/
theorem exists_avoiding_events {ι : Type*} (s : Finset ι) (event : ι → Ω → Prop)
    [∀ i ω, Decidable (event i ω)] (good : Ω → Prop) (p : ℝ)
    (hgood : ∀ᵐ ω ∂μ, good ω)
    (hint : ∀ i ∈ s, Integrable (fun ω ↦ if event i ω then (1 : ℝ) else 0) μ)
    (hprob : ∀ i ∈ s, (∫ ω, if event i ω then (1 : ℝ) else 0 ∂μ) ≤ p)
    (hsmall : (s.card : ℝ) * p < 1) : ∃ ω, good ω ∧ ∀ i ∈ s, ¬event i ω := by
  let count (ω : Ω) := (s.filter fun i ↦ event i ω).card
  have expand (ω : Ω) : (count ω : ℝ) = ∑ i ∈ s, if event i ω then (1 : ℝ) else 0 :=
    Finset.natCast_card_filter _ _
  have hsum : Integrable (fun ω ↦ (count ω : ℝ)) μ := by
    simp_rw [expand]
    exact integrable_finset_sum s hint
  have hmean : ∫ ω, (count ω : ℝ) ∂μ < 1 := by
    simp_rw [expand]
    rw [integral_finset_sum s hint]
    calc
      _ ≤ ∑ _i ∈ s, p := Finset.sum_le_sum hprob
      _ = (s.card : ℝ) * p := by simp
      _ < 1 := hsmall
  obtain ⟨ω, hw, hz⟩ := exists_zero_of_integral_lt_one count good hgood hsum hmean
  refine ⟨ω, hw, fun i hi hbad ↦ ?_⟩
  exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hbad⟩⟩)) hz

/-- Apply the event bound to the complete wave. A monochromatic event requires two equal
nonblank colours. The full-measure hypothesis excludes blanks at the endpoints. -/
theorem colourable_of_edge_prob {V κ : Type*} [DecidableEq κ]
    (edges : Finset (V × V)) (colour : Ω → V → Option κ) (fallback : κ) (p : ℝ)
    (hcomplete : ∀ᵐ ω ∂μ, ∀ e ∈ edges,
      (colour ω e.1).isSome = true ∧ (colour ω e.2).isSome = true)
    (hint : ∀ e ∈ edges, Integrable (fun ω ↦ if (colour ω e.1).isSome = true ∧
      colour ω e.1 = colour ω e.2 then (1 : ℝ) else 0) μ)
    (hprob : ∀ e ∈ edges, (∫ ω, if (colour ω e.1).isSome = true ∧
      colour ω e.1 = colour ω e.2 then (1 : ℝ) else 0 ∂μ) ≤ p)
    (hsmall : (edges.card : ℝ) * p < 1) : ∃ c : V → κ, ∀ e ∈ edges, c e.1 ≠ c e.2 := by
  obtain ⟨ω, hn, ha⟩ := exists_avoiding_events edges
    (fun e ω ↦ (colour ω e.1).isSome = true ∧ colour ω e.1 = colour ω e.2)
    _ p hcomplete hint hprob hsmall
  refine ⟨fun v ↦ (colour ω v).getD fallback, ?_⟩
  intro e he h
  apply ha e he
  refine ⟨(hn e he).1, ?_⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hn e he).1
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hn e he).2
  simpa [ha, hb] using h

end HadwigerNelson.Placement
