import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Ring

namespace ZetaSixth.Exponents

open scoped BigOperators

/-- Limiting degrees in §8.2 and Lemmas 82–89. The four dual degrees are sorted in
decreasing order. The separate mark is `mark` ((\mathfrak b)), and the dual
frequency degree (mathsf b) is derived below. -/
structure Degrees where
  ς : ℝ
  mark : ℝ
  g : ℝ
  r : ℝ
  i : ℝ
  tail : ℝ
  dual : Fin 4 → ℝ
  z : ℝ
  x : ℝ
  E : ℝ
  w : ℝ

noncomputable section

namespace Degrees

variable (q : Degrees)

/-- The display “Degrees” before Lemma 83, (sigma=[d]). -/
def sigma : ℝ := 1 - q.g - q.r

/-- The display “Degrees” before Lemma 83, (lambda). -/
def lambda : ℝ := 1 + q.ς - 3 * q.g - 4 * q.r - q.tail

/-- The display “Degrees” before Lemma 83, the required saving (	au). -/
def tau : ℝ := q.ς - 2 * q.g - 3 * q.r - (9 / 10) * q.tail

/-- The cutoff (mathsf B_*) in Lemma 84. -/
def splitBudget : ℝ := q.sigma / 2 + 2 * q.tau

/-- The largest dual degree (mathsf m) in Lemma 83. -/
def m : ℝ := q.dual 0

/-- The second largest dual degree (mathsf n) in Lemma 83. -/
def n : ℝ := q.dual 1

/-- The sum (mathsf j) of the two smallest dual degrees in Lemma 83. -/
def j : ℝ := q.dual 2 + q.dual 3

/-- The total dual degree (mathsf D) in Lemma 83. -/
def D : ℝ := q.m + q.n + q.j

/-- The first Poisson frequency degree (mathsf a) in Lemma 85. -/
def a : ℝ := q.sigma - q.n

/-- The second Poisson frequency degree (mathsf b) in Lemma 85. -/
def b : ℝ := q.sigma - q.m

/-- The degree (mathsf Z=[lf]) after the modulus reduction in §8.2. -/
def Z : ℝ := q.z + q.x

/-- The degree (mathsf y=[y_0]) after the modulus reduction in §8.2. -/
def y : ℝ := q.j - q.x

/-- The degree (mathsf C=[u']) after the modulus reduction in §8.2. -/
def C : ℝ := q.sigma - q.Z

/-- The required saving (mathsf u) in “Normalisation” after the modulus reduction. -/
def u : ℝ := q.j + q.tail / 10 - q.i - q.Z - q.E

/-- The raw exponent budget (mathsf B) in “Normalisation” after the modulus reduction. -/
def budget : ℝ := 2 * q.sigma + q.y - q.tau

/-- The degree (mathsf c=[C_0]) in the display before Lemma 86. -/
def c : ℝ := q.C - q.w

/-- The degree (mathsf d) of the (d_0) length in the display before Lemma 86. -/
def d : ℝ := q.a - q.E

/-- The degree (mathsf R=[R_0]) in the display before Lemma 86. -/
def R : ℝ := q.b + q.r + q.z + q.i + q.E

/-- The degree (mathsf N=[N_0]) in the display before Lemma 86. -/
def N : ℝ := 2 * q.r + q.y

/-- The degree (mathsf J=[T_0]) in Lemma 89. -/
def J : ℝ := q.C - q.d

/-- The represented level degree (mathsf A_*) in Lemma 89. -/
def level : ℝ := q.R + q.w

/-- The exceptional spectrum argument in equation (59), the display for (mathsf F_*). -/
def exceptional : ℝ := q.C + q.J + q.N - 3 * q.R / 2 - 2 * q.w

/-- The part of (mathsf F_*) before the three positive parts, Lemma 89(ii). -/
def representedBase : ℝ := q.d + q.R / 2 + q.b + q.w + (q.J + q.y) / 2

/-- The nonnegative dual degrees are sorted as in the “Degrees” paragraph.
The conductor degree is nonnegative and (0≤mathfrak i≤3mathfrak g+4mathfrak r)
and (mathsf D=lambda+mathfrak i) are from Lemmas 82–83. The remaining
constraints are from “Reduction of the modulus” and Lemma 87 ((w≤min(C,mathfrak b))). -/
def Admissible : Prop :=
  0 ≤ q.g ∧ 0 ≤ q.r ∧ 0 ≤ q.i ∧ 0 ≤ q.tail ∧ 0 ≤ q.sigma ∧
  (∀ a, 0 ≤ q.dual a) ∧ Antitone q.dual ∧
  q.i ≤ 3 * q.g + 4 * q.r ∧ q.D = q.lambda + q.i ∧
  0 ≤ q.z ∧ 0 ≤ q.x ∧ 0 ≤ q.E ∧ 0 ≤ q.w ∧
  0 ≤ q.y ∧ q.E ≤ q.Z ∧ q.E ≤ q.a ∧ q.w ≤ q.C ∧ q.w ≤ q.mark

/-- The mark cap of (mathcal P^{+*}), §8. -/
def markCap (ς : ℝ) : ℝ :=
  if ς < 1 / 10 then 1 / 2
  else if ς < 1 / 7 then max ((3 - 21 * ς) / 2) ((2 - 7 * ς) / 4)
  else if ς < 1 / 4 then (1 - 2 * ς) / 4
  else (1 - 3 * ς) / 2

/-- The domain (mathcal P^{+*}) in §8, in ((arsigma,mathfrak b)) coordinates. -/
def InMarkRegion : Prop := 0 < q.ς ∧ q.ς < 1 / 3 ∧ 0 < q.mark ∧ q.mark < markCap q.ς

/-- The trivial bound saves when either of these two margins is positive, Lemma 90. -/
def Trivial : Prop := 0 < -q.tau ∨ 0 < -q.u

/-- The split degrees of Lemma 84. The complement is the group with the larger degree. -/
def splitDegree (s : Finset (Fin 4)) : ℝ := ∑ a ∈ s, q.dual a

/-- One-variable or two-group unsigned margins, Lemma 84. -/
def Unsigned : Prop :=
  0 < q.m - q.sigma / 2 - q.tau ∨
  (0 < q.sigma - 4 * q.tau ∧ ∃ s : Finset (Fin 4),
    let small := q.splitDegree s
    let large := q.splitDegree sᶜ
    small ≤ large ∧ 0 < small - 2 * q.tau ∧ 0 < large - q.splitBudget)

/-- Diagonal spectral-square margin (mathsf P_0), Lemma 86. -/
def P0 : ℝ := q.b - q.j - q.tail / 5 + 2 * q.z + q.x + 2 * q.E

/-- First spectral-square margin (mathsf P_1), Lemma 86. -/
def P1 : ℝ := q.m - q.n / 2 - q.j - q.i - q.tail / 5 + (q.Z + q.E) / 2

/-- Second spectral-square margin (mathsf P_2), Lemma 86. -/
def P2 : ℝ := q.a / 2 - q.j - q.i / 2 - q.tail / 5 + 3 * q.z / 2 + q.x + q.E

/-- Third spectral-square margin (mathsf P_3), Lemma 86. -/
def P3 : ℝ :=
  (q.sigma + q.m) / 2 - 3 * q.j / 2 - (q.r + q.i) / 2 - q.tail / 5 +
    q.z / 2 + q.x / 2 + 3 * q.E / 2

/-- The spectral-square prerequisites and margins in Lemma 86. -/
def SpectralSquare : Prop :=
  0 < q.b - q.j - q.r ∧ 0 < q.P0 ∧ 0 < q.P2 ∧ 0 < q.P3 ∧
    (0 < q.P1 ∨ 0 < q.C - q.z - q.i - 2 * q.b - q.a)

/-- The seven affine terms of (mathcal K) in the display of Lemma 87. -/
def directTerms : List ℝ :=
  [q.c + q.w + (q.R + q.w) + q.c, q.c + q.w + (q.R + q.w) + (q.R + q.d),
    q.c + q.w + q.N + q.c, q.c + q.w + q.N + (q.R + q.d),
    2 * q.c + q.d + q.w + (q.R + q.w + q.R) / 2,
    2 * q.c + q.d + q.w + (q.N + q.R) / 2, 2 * q.d + q.N + q.R]

/-- The doubled direct margin at a term of (mathcal K), Lemma 87, with
the gain either (0) or the affine term (mathsf E-mathsf z). -/
def directMargin (k gain : ℝ) : ℝ :=
  2 * q.budget - (q.y + q.b + q.w - q.z + k - gain)

/-- Lemma 87 without the optional gain. -/
def Direct : Prop := ∀ k ∈ q.directTerms, 0 < q.directMargin k 0

/-- Lemma 87 with the gain ((mathsf E-mathsf z)_+), expressed as a
disjunction of conjunctions of strict affine inequalities. -/
def DirectWithGain : Prop :=
  q.Direct ∨ (∀ k ∈ q.directTerms, 0 < q.directMargin k (q.E - q.z))

/-- Both reciprocal-completion margins in Lemma 88. -/
def Reciprocal : Prop := 0 < q.C / 2 - q.u ∧ 0 < q.b - q.C / 2 - q.u

/-- One of the eight affine margins from the display for (mathsf F_*) in
Lemma 89(ii), by choosing either 0 or the affine argument in each positive part. -/
def representedMargin (jTerm nTerm exceptionTerm : Bool) : ℝ :=
  q.budget - (q.representedBase
    + (if jTerm then (q.J - q.level) / 2 else 0)
    + (if nTerm then (q.N - q.level) / 2 else 0)
    + (if exceptionTerm then (7 / 32) * q.exceptional else 0))

/-- The vanishing alternative and all eight strict margins of Lemma 89. -/
def RepresentedLevel : Prop :=
  0 < -q.J ∨ ∀ jTerm nTerm exceptionTerm : Bool,
    0 < q.representedMargin jTerm nTerm exceptionTerm

/-- The range of Lemma 90(i), within (mathcal P^{+*}). -/
def BandI : Prop := q.ς < 1 / 10

/-- The range and mark cap of Lemma 90(ii). -/
def BandII : Prop := 1 / 10 ≤ q.ς ∧ q.ς < 1 / 8 ∧ q.mark < (3 - 21 * q.ς) / 2

/-- The three ranges and respective caps of Lemma 90(iii). -/
def BandIII : Prop :=
  (1 / 10 ≤ q.ς ∧ q.ς < 1 / 7 ∧ q.mark < (2 - 7 * q.ς) / 4) ∨
  (1 / 7 ≤ q.ς ∧ q.ς < 1 / 4 ∧ q.mark < (1 - 2 * q.ς) / 4) ∨
  (1 / 4 ≤ q.ς ∧ q.ς < 1 / 3 ∧ q.mark < (1 - 3 * q.ς) / 2)

end Degrees

/-- The strict saving alternatives of Lemma 90(i)–(iii). -/
def Lemma90 : Prop := ∀ q : Degrees, q.Admissible → q.InMarkRegion →
  (q.BandI → q.Trivial ∨ q.Unsigned ∨ q.SpectralSquare) ∧
  (q.BandII → q.Trivial ∨ q.Unsigned ∨ q.SpectralSquare ∨ q.Direct) ∧
  (q.BandIII → q.Trivial ∨ q.Unsigned ∨ q.Reciprocal ∨ q.DirectWithGain ∨ q.RepresentedLevel)

/-- The covering conclusion of Lemma 90 on all of (mathcal P^{+*}). -/
def Covering : Prop := ∀ q : Degrees, q.Admissible → q.InMarkRegion →
  q.Trivial ∨ q.Unsigned ∨ q.SpectralSquare ∨ q.DirectWithGain ∨
    q.Reciprocal ∨ q.RepresentedLevel

/-- The comparison immediately after Lemma 90, between the two middle-band caps. -/
theorem markCapDifference (ς : ℝ) :
    (3 - 21 * ς) / 2 - (2 - 7 * ς) / 4 = (4 - 35 * ς) / 4 := by ring

end

end ZetaSixth.Exponents
