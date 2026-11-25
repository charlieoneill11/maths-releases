import LeastPrime.Bounds
import LeastPrime.TheoremAssembly

/-! The two headline theorems, conditional on their cited analytic inputs. -/

namespace LeastPrime

/-- The divisor-density lower bound uses only the cited Donnelly–Grimmett limit. -/
theorem density_lower_of_donnellyGrimmett (h : DonnellyGrimmettInput) : density_lower :=
  density_lower_of_numerics h p6_Tin

/-- The divisor-density upper bound uses only the cited Donnelly–Grimmett limit. -/
theorem density_upper_of_donnellyGrimmett (h : DonnellyGrimmettInput) : density_upper :=
  density_upper_of_numerics h q5_Tout

theorem density_lower_of_cited (h : CitedFacts) : density_lower :=
  density_lower_of_donnellyGrimmett h.donnellyGrimmett

theorem density_upper_of_cited (h : CitedFacts) : density_upper :=
  density_upper_of_donnellyGrimmett h.donnellyGrimmett

/-- The least-prime theorem with the explicit constant `C = 4`. -/
theorem main_four_of_cited (h : CitedFacts) : ∃ δ : ℝ, 0 < δ ∧ mainBound 4 δ :=
  main_four_of_numerics h p6_Tin

theorem main_of_cited (h : CitedFacts) : main :=
  main_of_numerics h p6_Tin

end LeastPrime
