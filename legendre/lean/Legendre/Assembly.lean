import Legendre.Bridge
import Legendre.Elementary

namespace Legendre

/-- Theorem 4, the large range. -/
theorem outer_of (hRH : RiemannHypothesis) (h : CitedFacts) : OuterStatement := by
  intro x hx
  by_cases hfar : 6 * 10 ^ 14 ≤ x
  · exact far_range hRH h x hfar
  · exact bridge_range hRH h x hx (le_of_not_ge hfar)

/-- Theorem 1, with RH and the cited and computed inputs made explicit. -/
theorem main_of (hRH : RiemannHypothesis) (h : CitedFacts) (c : ComputationClaims) : MainStatement :=
  main_of_outer (outer_of hRH h) h c

end Legendre
