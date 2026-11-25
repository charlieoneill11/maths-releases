import Legendre

/-! Lean declarations corresponding to the table in `BLUEPRINT.md`. -/

namespace Legendre

#check powerEndpoint_ne_prime
#check powerInterval_iff
#check prime_in_shifted_square
#check low_range
#check square_interval_nested
#check prime_in_cms_interval
#check far_range
#check CosineTest
#check cosine_fourier_spec
#check smoothed_explicit_formula
#check zeroCount_error
#check zero_sum_bound
#check gap_condition
#check shoulder_lengths
#check twelve_mode_bounds
#check twelve_mode_cell_bounds
#check shoulder_sum_bound
#check bridge_row_checks
#check bridge_error_bounds
#check bridge_range
#check finite_range

example : RiemannHypothesis → CitedFacts → OuterStatement := outer_of
example : CitedFacts → ComputationClaims → SquaresStatement := squares_of
example : RiemannHypothesis → CitedFacts → ComputationClaims → MainStatement := main_of

end Legendre
