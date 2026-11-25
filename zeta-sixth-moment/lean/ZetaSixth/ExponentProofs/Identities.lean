import ZetaSixth.Exponents
import Mathlib.Tactic.Linarith

namespace ZetaSixth.Exponents.Identities

variable (q : Degrees)

-- Lemma 83 and the consequences of Lemma 84.

theorem Y_degree (hD : q.D = q.lambda + q.i) :
    q.i + 3 * q.sigma - q.r - (2 - q.ς) = q.D + q.tail := by
  rw [hD]
  unfold Degrees.sigma Degrees.lambda
  ring

theorem sigma_sub_two_tau :
    q.sigma - 2 * q.tau = 1 - 2 * q.ς + 3 * q.g + 5 * q.r + 9 / 5 * q.tail := by
  unfold Degrees.sigma Degrees.tau
  ring

theorem sigma_sub_four_tau :
    q.sigma - 4 * q.tau = 1 - 4 * q.ς + 7 * q.g + 11 * q.r + 18 / 5 * q.tail := by
  unfold Degrees.sigma Degrees.tau
  ring

theorem j_eq (hD : q.D = q.lambda + q.i) : q.j = q.lambda + q.i - q.m - q.n := by
  unfold Degrees.D at hD
  linarith only [hD]

-- Lemma 85 and the reduction and normalisation paragraphs after it.

theorem double_poisson_saving (hD : q.D = q.lambda + q.i) :
    q.tau + q.sigma - q.m - q.n = q.j + q.tail / 10 - q.i := by
  rw [j_eq q hD]
  unfold Degrees.tau Degrees.sigma Degrees.lambda
  ring

theorem required_saving (hD : q.D = q.lambda + q.i) :
    q.tau + q.sigma - q.m - q.n - q.Z - q.E = q.u := by
  unfold Degrees.u
  rw [double_poisson_saving q hD]

theorem reduced_budget (hD : q.D = q.lambda + q.i) :
    q.C + q.y + q.a - q.E + q.b - q.u = q.budget := by
  rw [← required_saving q hD]
  unfold Degrees.C Degrees.a Degrees.b Degrees.budget
  ring

-- The allowable exponent and four square margins of Lemma 86.

noncomputable def squareBudget : ℝ :=
  q.sigma + q.z - q.x + q.a + 2 * q.b - q.tail / 5 + q.E

noncomputable def squareFrequency : ℝ := q.z + q.i + q.E + 2 * q.b

noncomputable def squareLength : ℝ := q.r + q.y + q.b

theorem square_budget :
    q.C + (q.a - q.E) + 2 * q.y + 2 * q.b -
      2 * (q.j + q.tail / 10 - q.Z - q.E) = squareBudget q := by
  unfold Degrees.C Degrees.y Degrees.Z squareBudget
  ring

theorem square_margin_0 :
    squareBudget q - (q.C + (q.a - q.E) + q.y + q.b) = q.P0 := by
  unfold squareBudget Degrees.C Degrees.y Degrees.Z Degrees.P0
  ring

theorem square_margin_1 :
    squareBudget q - (q.y + q.b) - (q.C + 2 * squareFrequency q + (q.a - q.E)) / 2 =
      q.P1 := by
  unfold squareBudget squareFrequency Degrees.C Degrees.y Degrees.P1 Degrees.Z Degrees.a Degrees.b
  ring

theorem square_margin_2 :
    squareBudget q - (q.y + q.b) - (2 * q.C + (q.a - q.E) + squareFrequency q) / 2 =
      q.P2 := by
  unfold squareBudget squareFrequency Degrees.C Degrees.y Degrees.Z Degrees.P2
  ring

theorem square_margin_3 :
    squareBudget q - (q.y + q.b) -
      (2 * (q.a - q.E) + squareLength q + squareFrequency q) / 2 = q.P3 := by
  unfold squareBudget squareLength squareFrequency Degrees.y Degrees.P3 Degrees.a Degrees.b
  ring

-- The seven direct margins from equation (58) and their expansions in Lemma 90(ii).
-- Each margin here is doubled, including the displayed expansion for M₁.

theorem direct_Rw_c (hD : q.D = q.lambda + q.i) :
    q.directMargin (q.c + q.w + (q.R + q.w) + q.c) 0 =
      1 - q.ς + q.g + q.r + 4 / 5 * q.tail + (q.m - q.n) + (q.Z - q.E) + q.z - q.w := by
  unfold Degrees.directMargin Degrees.budget Degrees.c Degrees.R Degrees.b Degrees.C Degrees.y
    Degrees.tau Degrees.sigma Degrees.Z
  rw [j_eq q hD]
  unfold Degrees.lambda
  ring

theorem direct_Rw_Rd (hD : q.D = q.lambda + q.i) :
    q.directMargin (q.c + q.w + (q.R + q.w) + (q.R + q.d)) 0 =
      2 * (q.m - q.ς / 2 + q.g + q.r / 2 + 2 / 5 * q.tail - q.w - q.i / 2 - q.E / 2) := by
  unfold Degrees.directMargin Degrees.budget Degrees.c Degrees.R Degrees.d Degrees.a Degrees.b
    Degrees.C Degrees.y Degrees.tau Degrees.sigma Degrees.Z
  rw [j_eq q hD]
  unfold Degrees.lambda
  ring

theorem direct_N_c :
    q.directMargin (q.c + q.w + q.N + q.c) 0 =
      1 - 2 * q.ς + 3 * q.g + 3 * q.r + 9 / 5 * q.tail + q.m + 2 * q.x + 3 * q.z := by
  unfold Degrees.directMargin Degrees.budget Degrees.c Degrees.N Degrees.b Degrees.C
    Degrees.tau Degrees.sigma Degrees.Z
  ring

theorem direct_N_Rd :
    q.directMargin (q.c + q.w + q.N + (q.R + q.d)) 0 =
      2 * q.m + q.n - 2 * q.ς + 4 * q.g + 3 * q.r - q.i + 9 / 5 * q.tail + q.x + q.z - q.w := by
  unfold Degrees.directMargin Degrees.budget Degrees.c Degrees.N Degrees.R Degrees.d Degrees.a
    Degrees.b Degrees.C Degrees.tau Degrees.sigma Degrees.Z
  ring

theorem direct_prime_Rw (hD : q.D = q.lambda + q.i) :
    q.directMargin (2 * q.c + q.d + q.w + (q.R + q.w + q.R) / 2) 0 =
      q.m - q.ς + 2 * q.g + 2 * q.r + 4 / 5 * q.tail - q.w / 2 + q.Z + q.z := by
  unfold Degrees.directMargin Degrees.budget Degrees.c Degrees.R Degrees.d Degrees.a Degrees.b
    Degrees.C Degrees.y Degrees.tau Degrees.sigma Degrees.Z
  rw [j_eq q hD]
  unfold Degrees.lambda
  ring

theorem direct_prime_N (hD : q.D = q.lambda + q.i) :
    q.directMargin (2 * q.c + q.d + q.w + (q.N + q.R) / 2) 0 =
      q.m + q.n / 2 - 3 / 2 * q.ς + 3 * q.g + 3 * q.r + 13 / 10 * q.tail +
        3 / 2 * q.x + 5 / 2 * q.z + q.E / 2 := by
  unfold Degrees.directMargin Degrees.budget Degrees.c Degrees.N Degrees.R Degrees.d Degrees.a
    Degrees.b Degrees.C Degrees.y Degrees.tau Degrees.sigma Degrees.Z
  rw [j_eq q hD]
  unfold Degrees.lambda
  ring

theorem direct_double_prime :
    q.directMargin (2 * q.d + q.N + q.R) 0 =
      2 * (q.m + q.n) - 2 * q.tau - 3 * q.r - q.i + q.E - q.w := by
  unfold Degrees.directMargin Degrees.budget Degrees.N Degrees.R Degrees.d Degrees.a Degrees.b
  ring

-- Lemma 89 and the represented-level normalisation.

noncomputable def X : ℝ := q.C + q.R / 2 - (q.J + q.N) / 2

theorem represented_degree : q.J = q.n - q.Z + q.E := by
  unfold Degrees.J Degrees.C Degrees.d Degrees.a
  ring

theorem two_X (hD : q.D = q.lambda + q.i) : 2 * X q = 2 - q.ς + q.tail := by
  unfold X Degrees.J Degrees.C Degrees.R Degrees.N Degrees.d Degrees.a Degrees.b
    Degrees.y Degrees.Z Degrees.sigma
  rw [j_eq q hD]
  unfold Degrees.lambda
  ring

theorem exceptional_argument :
    X q - (2 * (q.R + q.w) - (3 / 2) * (q.J + q.N)) = q.exceptional := by
  unfold X Degrees.exceptional
  ring

theorem C_sub_J : q.C - q.J = q.d := by
  unfold Degrees.J
  ring

theorem represented_slope : (3 / 2 : ℚ) - 1 / 2 - 1 / 2 - (3 / 2) * (7 / 32) = 11 / 64 := by
  norm_num

-- The affine expansions in the preliminaries and Steps 1 and 2 of Lemma 90.

theorem two_thirds_lambda_sub_split :
    2 / 3 * q.lambda - q.splitBudget =
      1 / 6 - 4 / 3 * q.ς + 5 / 2 * q.g + 23 / 6 * q.r + 17 / 15 * q.tail := by
  unfold Degrees.lambda Degrees.splitBudget Degrees.sigma Degrees.tau
  ring

theorem lambda_gap_sub_four_tau :
    q.lambda - q.splitBudget - 4 * q.tau =
      1 / 2 - 5 * q.ς + 19 / 2 * q.g + 29 / 2 * q.r + 22 / 5 * q.tail := by
  unfold Degrees.lambda Degrees.splitBudget Degrees.sigma Degrees.tau
  ring

theorem lambda_sub_four_tau :
    q.lambda - 4 * q.tau = 1 - 3 * q.ς + 5 * q.g + 8 * q.r + 13 / 5 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

theorem sigma_sub_split_sub_two_tau :
    q.sigma - q.splitBudget - 2 * q.tau = q.sigma / 2 - 4 * q.tau := by
  unfold Degrees.splitBudget
  ring

theorem C_lower :
    q.sigma - (1 + q.ς) / 2 - q.tail / 10 =
      1 / 2 - q.ς / 2 - q.g - q.r - q.tail / 10 := by
  unfold Degrees.sigma
  ring

theorem step2_b_sub_j :
    q.sigma / 2 - 3 * q.tau - 2 * q.r - q.tail / 5 =
      1 / 2 - 3 * q.ς + 11 / 2 * q.g + 13 / 2 * q.r + 5 / 2 * q.tail := by
  unfold Degrees.sigma Degrees.tau
  ring

theorem step2_P1 :
    q.lambda - 10 * q.tau - 4 * (3 * q.g + 4 * q.r) - 4 / 5 * q.tail =
      1 - 9 * q.ς + 5 * q.g + 10 * q.r + 36 / 5 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

theorem step2_P2 :
    2 * q.sigma - (1 + q.ς) - 6 * q.tau - 2 * (3 * q.g + 4 * q.r) - 4 / 5 * q.tail =
      1 - 7 * q.ς + 4 * q.g + 8 * q.r + 23 / 5 * q.tail := by
  unfold Degrees.sigma Degrees.tau
  ring

theorem step2_P3 :
    q.sigma / 2 - 3 * q.tau - (q.r + (3 * q.g + 4 * q.r)) / 2 - q.tail / 5 =
      1 / 2 - 3 * q.ς + 4 * q.g + 6 * q.r + 5 / 2 * q.tail := by
  unfold Degrees.sigma Degrees.tau
  ring

-- Lemma 90(ii), j ≤ 2τ.

theorem case1_M1_first :
    (q.lambda - 2 * q.tau) / 2 - q.ς / 2 + q.g + q.r / 2 + 2 / 5 * q.tail -
      (3 * q.g + 4 * q.r) / 2 = 1 / 2 - q.ς - q.r / 2 + 4 / 5 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

theorem case1_M1_second :
    1 / 2 - q.ς - q.r / 2 + 4 / 5 * q.tail -
      ((9 * q.ς - 1 - 5 * q.g - 10 * q.r - (36 / 5) * q.tail) / 2) / 2 =
      3 / 4 - 13 / 4 * q.ς + 5 / 4 * q.g + 2 * q.r + 13 / 5 * q.tail := by
  ring

theorem case1_mark :
    3 / 4 - 13 / 4 * q.ς - (3 - 21 * q.ς) / 2 = (29 * q.ς - 3) / 4 := by
  ring

theorem case1_M2 :
    (q.lambda - 2 * q.tau) / 2 - q.ς =
      1 / 2 - 3 / 2 * q.ς + q.g / 2 + q.r + 2 / 5 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

theorem case1_M3 :
    2 * (q.lambda - 2 * q.tau) - 2 * q.tau - 3 * q.r - (3 * q.g + 4 * q.r) =
      2 - 4 * q.ς + 3 * q.g + 3 * q.r + 17 / 5 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

-- Lemma 90(ii), j > 2τ.

theorem case2_b_sub_j :
    q.sigma / 2 - 4 * q.tau - 2 * q.r - q.tail / 5 =
      1 / 2 - 4 * q.ς + 15 / 2 * q.g + 19 / 2 * q.r + 17 / 5 * q.tail := by
  unfold Degrees.sigma Degrees.tau
  ring

theorem case2_P1 :
    (q.lambda - 6 * q.tau) - q.tau - 4 * q.tau - (3 * q.g + 4 * q.r) - q.tail / 5 =
      1 - 10 * q.ς + 16 * q.g + 25 * q.r + 87 / 10 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

theorem case2_P2 :
    (q.sigma - 2 * q.tau) / 2 - 4 * q.tau - (3 * q.g + 4 * q.r) / 2 - q.tail / 5 =
      1 / 2 - 5 * q.ς + 8 * q.g + 25 / 2 * q.r + 43 / 10 * q.tail := by
  unfold Degrees.sigma Degrees.tau
  ring

theorem case2_P3 :
    (q.sigma + q.lambda - 6 * q.tau) / 2 - 3 / 2 * (4 * q.tau) -
      (q.r + (3 * q.g + 4 * q.r)) / 2 - q.tail / 5 =
      1 - 17 / 2 * q.ς + 29 / 2 * q.g + 22 * q.r + 37 / 5 * q.tail := by
  unfold Degrees.sigma Degrees.lambda Degrees.tau
  ring

theorem case2_M1 :
    q.lambda - 6 * q.tau - q.ς / 2 + q.g + q.r / 2 + 2 / 5 * q.tail -
      (3 * q.g + 4 * q.r) / 2 =
      1 - 11 / 2 * q.ς + 17 / 2 * q.g + 25 / 2 * q.r + 24 / 5 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

theorem case2_mark :
    1 - 11 / 2 * q.ς - (3 - 21 * q.ς) / 2 = 5 * q.ς - 1 / 2 := by
  ring

theorem case2_M2 :
    q.lambda - 6 * q.tau - q.ς =
      1 - 6 * q.ς + 9 * q.g + 14 * q.r + 22 / 5 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

theorem case2_M3 :
    2 * q.lambda - 10 * q.tau - 3 * q.r =
      2 - 8 * q.ς + 14 * q.g + 19 * q.r + 7 * q.tail := by
  unfold Degrees.lambda Degrees.tau
  ring

end ZetaSixth.Exponents.Identities
