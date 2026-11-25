import Legendre.AnalyticData

namespace Legendre

/-- The entries of a row of Table 1. -/
structure BridgeRow where
  lo : ℕ
  hi : ℕ
  logLo : ℚ
  logHi : ℚ
  scaleLo : ℚ
  chargeHi : ℚ
  k : ℚ
  valueLo : ℚ
  derivLo : ℚ

def firstRow : BridgeRow :=
  ⟨35 * 10 ^ 12, 37 * 10 ^ 12, 34.2, 34.4, 24.877, 0.098159, 0.90184, 0.0030, 1.4776⟩

def secondRow : BridgeRow :=
  ⟨37 * 10 ^ 12, 600 * 10 ^ 12, 34.2, 37.5, 25.015, 0.098420, 0.90150, 0.0769, 1.4892⟩

/-- Soundness conclusions for checks (i)–(v) of Proposition 22. -/
structure BridgeRowChecks (row : BridgeRow) (e : ℕ → ℚ) (b : ℕ → ℝ) : Prop where
  logLo : (row.logLo : ℝ) < 1.1 * Real.log row.lo
  logHi : 1.1 * Real.log ((row.hi : ℝ) + 1) < (row.logHi : ℝ)
  scaleLo : (row.scaleLo : ℝ) < 1.1 * (row.lo : ℝ) ^ ((1 : ℝ) / 10) *
    ((row.lo : ℝ) / ((row.lo : ℝ) + 1))
  lengthLo : 4000 * U₁ * 10 ^ 12 < (row.scaleLo : ℝ) * (row.lo : ℝ) *
    (row.lo : ℝ) ^ ((1 : ℝ) / 10)
  offsets : ∀ j : ℕ, j ∈ Finset.Icc 1 4000 → e (j + 1) < e j →
    b j ≤ Real.log ((row.scaleLo : ℝ) * ((j : ℝ) / 4000)) - Real.log U₁ ∧
      0 < (row.logLo : ℝ) + b j
  chargeHi : shoulderCharge e b row.logLo row.logHi < (row.chargeHi : ℝ)
  pole : (row.k : ℝ) < 1.00000063 - (row.chargeHi : ℝ)
  comparison : (row.valueLo : ℝ) < bridgeComparison row.k row.lo
  derivative : (row.derivLo : ℝ) < 0.11 * (row.k : ℝ) * (row.lo : ℝ) ^ ((1 : ℝ) / 10) *
    ((row.lo : ℝ) / ((row.lo : ℝ) + 1)) - 0.765870

end Legendre
