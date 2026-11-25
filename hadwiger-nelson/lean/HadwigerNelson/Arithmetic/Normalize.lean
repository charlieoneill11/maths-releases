import HadwigerNelson.Arithmetic.Rounding

/-! Lower bounds for signed angular means with rational enclosures of the period. -/

namespace HadwigerNelson.Arithmetic

/-- Choose the denominator outward according to the sign of the integrated quantity. -/
def signedScale (a q low high denom : Int) : Int :=
  (a*q*denom) / (if a < 0 then low else high)

/-- The exact period P lies between low/denom and high/denom. -/
theorem signedScale_le (a q low high denom : Int) (P : ℝ)
    (hq : 0 ≤ q) (hden : 0 < denom) (hlo : 0 < low)
    (hpl : (low:ℝ) ≤ denom*P) (hph : (denom:ℝ)*P ≤ high) :
    (signedScale a q low high denom : ℝ) ≤ (a:ℝ)*q/P := by
  have hr : (0:ℝ) < denom := by exact_mod_cast hden
  have hl : (0:ℝ) < low := by exact_mod_cast hlo
  have hh : (0:ℝ) < high := hl.trans_le (hpl.trans hph)
  have hp : 0 < P := (mul_pos_iff_of_pos_left hr).mp (hl.trans_le hpl)
  have hq' : (0:ℝ) ≤ q := by exact_mod_cast hq
  unfold signedScale
  split_ifs with ha
  · apply (floorDiv_le_real _ hlo).trans
    apply (div_le_div_iff₀ hl hp).2
    push_cast
    have ha' : (a:ℝ) < 0 := by exact_mod_cast ha
    have := mul_le_mul_of_nonpos_left hpl (mul_nonpos_of_nonpos_of_nonneg ha'.le hq')
    linarith only [this]
  · apply (floorDiv_le_real _ (by exact_mod_cast hh)).trans
    apply (div_le_div_iff₀ hh hp).2
    push_cast
    have ha' : (0:ℝ) ≤ a := by exact_mod_cast (le_of_not_gt ha)
    have := mul_le_mul_of_nonneg_left hph (mul_nonneg ha' hq')
    linarith only [this]

end HadwigerNelson.Arithmetic
