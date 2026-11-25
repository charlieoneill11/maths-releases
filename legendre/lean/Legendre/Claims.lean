import Legendre.Statement

namespace Legendre

/-- The portions of the November 2026 computation used in Theorems 1 and 2.
See §5.3–5.4 and `legendre/computation/COVERAGE.md` in `maths-releases`. -/
structure ComputationClaims : Prop where
  /-- The square interval witnesses beyond the Sorenson–Webster prefix. -/
  squares : ∀ m : ℕ, 70_500_000_000_000 < m → m ≤ 10 ^ 14 →
    ∃ p : ℕ, p.Prime ∧ m ^ 2 < p ∧ p < (m + 1) ^ 2
  /-- The integer power interval witnesses beyond the square nesting range. -/
  powers : ∀ n : ℕ, 5_336_699_231_206 < n → n < 35 * 10 ^ 12 →
    ∃ p : ℕ, p.Prime ∧ n ^ 11 < p ^ 5 ∧ p ^ 5 < (n + 1) ^ 11

end Legendre
