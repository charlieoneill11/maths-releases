import Legendre.Arithmetic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Legendre.Arithmetic

open scoped BigOperators

private def logSeries (n : ℕ) (z : ℚ) : ℚ :=
  ∑ j ∈ Finset.range n, z ^ (2 * j + 1) / (2 * (j : ℚ) + 1)

private def logReduced (q : ℚ) : Bounds :=
  let z := (q - 1) / (q + 1)
  let approximation := logSeries 24 z
  ⟨2 * approximation, 2 * (approximation + z ^ 49 / (1 - z ^ 2))⟩

private theorem logReduced_sound {q : ℚ} (hl : 1 ≤ q) (hu : q ≤ 2) :
    (logReduced q).Encloses (Real.log (q : ℝ)) := by
  let z : ℚ := (q - 1) / (q + 1)
  have hl' : 1 ≤ (q : ℝ) := by exact_mod_cast hl
  have hu' : (q : ℝ) ≤ 2 := by exact_mod_cast hu
  have hzp : (z : ℝ) = ((q : ℝ) - 1) / ((q : ℝ) + 1) := by simp [z]
  have hz₀ : 0 ≤ (z : ℝ) := by
    rw [hzp]
    exact div_nonneg (sub_nonneg.mpr hl') (by positivity)
  have hz₁ : (z : ℝ) < 1 := by
    have hthird : (z : ℝ) ≤ 1 / 3 := by
      rw [hzp, div_le_iff₀ (by positivity)]
      linarith
    exact hthird.trans_lt (by norm_num)
  have hratio : (1 + (z : ℝ)) / (1 - (z : ℝ)) = q := by
    rw [hzp]
    have hne : (q : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hne]
    ring
  have hlower := Real.sum_range_le_log_div hz₀ hz₁ 24
  have hupper := Real.log_div_le_sum_range_add hz₀ hz₁ 24
  rw [hratio] at hlower hupper
  change ((2 * logSeries 24 z : ℚ) : ℝ) ≤ _ ∧ _ ≤
    ((2 * (logSeries 24 z + z ^ 49 / (1 - z ^ 2)) : ℚ) : ℝ)
  push_cast [logSeries]
  constructor <;> linarith

private def normalizeLog : ℕ → ℚ → ℕ × ℚ
  | 0, q => (0, q)
  | fuel + 1, q =>
    if q < 2 then (0, q) else
      let (n, r) := normalizeLog fuel (q / 2)
      (n + 1, r)

private theorem normalizeLog_eq (fuel : ℕ) (q : ℚ) :
    q = (2 : ℚ) ^ (normalizeLog fuel q).1 * (normalizeLog fuel q).2 := by
  induction fuel generalizing q with
  | zero => simp [normalizeLog]
  | succ fuel ih =>
    simp only [normalizeLog]
    split
    · simp
    · rcases h : normalizeLog fuel (q / 2) with ⟨n, r⟩
      have hqr := ih (q / 2)
      rw [h] at hqr
      change q / 2 = 2 ^ n * r at hqr
      change q = 2 ^ (n + 1) * r
      rw [pow_succ]
      linarith

private def logCoarse (q : ℚ) : Bounds := ⟨1 - q⁻¹, q - 1⟩

private theorem logCoarse_sound {q : ℚ} (hq : 0 < q) :
    (logCoarse q).Encloses (Real.log (q : ℝ)) := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hq')
  rw [Real.log_inv] at h
  constructor
  · simpa [logCoarse] using (show 1 - (q : ℝ)⁻¹ ≤ Real.log q by linarith)
  · simpa [logCoarse] using Real.log_le_sub_one_of_pos hq'

private def logAtLeastOne (q : ℚ) : Bounds :=
  let (n, r) := normalizeLog (q.num.natAbs.log2 + 1) q
  if 1 ≤ r ∧ r ≤ 2 then (logReduced r).add ((logReduced 2).smul n) else logCoarse q

private theorem logAtLeastOne_sound {q : ℚ} (hq : 1 ≤ q) :
    (logAtLeastOne q).Encloses (Real.log (q : ℝ)) := by
  unfold logAtLeastOne
  rcases h : normalizeLog (q.num.natAbs.log2 + 1) q with ⟨n, r⟩
  dsimp only
  split
  · rename_i hr
    have hr₀ : (r : ℝ) ≠ 0 := by
      have : 1 ≤ (r : ℝ) := by exact_mod_cast hr.1
      positivity
    have hqr := normalizeLog_eq (q.num.natAbs.log2 + 1) q
    rw [h] at hqr
    have heq : (q : ℝ) = (2 : ℝ) ^ n * (r : ℝ) := by exact_mod_cast hqr
    rw [heq, Real.log_mul (by positivity) hr₀, Real.log_pow, add_comm]
    exact Bounds.add_sound (logReduced_sound hr.1 hr.2)
      (Bounds.smul_sound n (logReduced_sound (by norm_num) le_rfl))
  · exact logCoarse_sound (by linarith)

private def logScale : ℕ := 2 ^ 200

/-- Enclose the logarithm of a positive rational and round out to multiples of `2⁻²⁰⁰`. -/
def logBounds (q : ℚ) : Bounds :=
  (if q < 1 then (logAtLeastOne q⁻¹).neg else logAtLeastOne q).round logScale

theorem logBounds_sound (q : ℚ) (hq : 0 < q) : (logBounds q).Encloses (Real.log (q : ℝ)) := by
  apply Bounds.round_sound _ _ (by unfold logScale; positivity)
  split
  · rename_i hq₁
    have hinv : 1 ≤ q⁻¹ := (one_le_inv₀ hq).mpr hq₁.le
    simpa only [Rat.cast_inv, Real.log_inv, neg_neg] using Bounds.neg_sound (logAtLeastOne_sound hinv)
  · exact logAtLeastOne_sound (by linarith)

end Legendre.Arithmetic
