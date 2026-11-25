import Legendre.BridgeContradiction
import Legendre.Gap
import Legendre.Native.BridgeNumeric
import Legendre.Native.ShoulderGrid
import Legendre.ShoulderSum
import Legendre.Twelve

namespace Legendre

open Arithmetic

theorem bridge_row_checks :
    ∃ (e : ℕ → ℚ) (b₁ b₂ : ℕ → ℝ), ShoulderSteps e ∧
      BridgeRowChecks firstRow e b₁ ∧ BridgeRowChecks secondRow e b₂ :=
  ⟨shoulderHeight, _, _, shoulderHeight_steps, firstRow_verified shoulderHeight_steps,
    secondRow_verified shoulderHeight_steps⟩

/-- Proposition 22, the two rows of Table 1 cover the interval before the CMS range. -/
theorem bridge_range (hRH : RiemannHypothesis) (h : CitedFacts)
    (x : ℝ) (hx₁ : 35 * 10 ^ 12 ≤ x) (hx₂ : x ≤ 6 * 10 ^ 14) :
    PrimeIn (x ^ ((11 : ℝ) / 5)) ((x + 1) ^ ((11 : ℝ) / 5)) := by
  let w := Window.ofBase x
  obtain ⟨e, b₁, b₂, he, hr₁, hr₂⟩ := bridge_row_checks
  have hwin : WindowBounds w twelveMode.K := (bridge_window_bounds hx₁ hx₂).1
  have hweight : twelveMode.weightSum < 1 := by rw [twelveMode_weightSum]; norm_num
  have hmass : twelveMode.mass < 4 := by
    refine twelveMode.mass_le.trans_lt ?_
    rw [twelveMode_K, twelveMode_weightSum]
    norm_num
  have hGap := fun hNone ↦ gap_condition hRH h twelveMode
    (by norm_num) (by norm_num) hweight hmass w hwin hNone
  have solve (row : BridgeRow) (b : ℕ → ℝ) (hr : BridgeRowChecks row e b)
      (hl : 0 < row.lo) (hp : 0 < row.scaleLo) (hk : 0 ≤ row.k)
      (hv : 0 ≤ row.valueLo) (hdv : 0 ≤ row.derivLo)
      (hlo : (0 : ℝ) < row.logLo) (hhi : (0 : ℝ) < row.logHi) (hh : (row.logHi : ℝ) ≤ 37.5)
      (hxl : (row.lo : ℝ) ≤ x) (hxr : x ≤ (row.hi : ℝ)) :
      PrimeIn (x ^ ((11 : ℝ) / 5)) ((x + 1) ^ ((11 : ℝ) / 5)) := by
    obtain ⟨hL₁, hL₂, hP, hW⟩ := hr.window_bounds hl hp hxl hxr
    have hp' : (0 : ℝ) < row.scaleLo := by exact_mod_cast hp
    have hS := shoulder_sum_bound h x hx₁ hx₂ e he row.scaleLo row.logLo row.logHi
      hp' hlo hhi hP hL₁ hL₂ hW b hr.offsets
    exact bridge_case hx₁ hx₂ row e b he hr twelve_mode_bounds hl hp hk hv hdv hh hxl hxr hS hGap
  by_cases hxmid : x ≤ 37 * 10 ^ 12
  · apply solve firstRow b₁ hr₁ <;> norm_num [firstRow] at * <;> assumption
  · have hxmid' : 37 * 10 ^ 12 ≤ x := le_of_not_ge hxmid
    apply solve secondRow b₂ hr₂ <;> norm_num [secondRow] at * <;> assumption

end Legendre
