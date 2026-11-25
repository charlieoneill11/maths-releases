import Chowla.CheckerArithmetic
import Chowla.Rows
import Mathlib.Data.List.Dedup

namespace Chowla.Checker

/-- One way to leave some positions of each row unmatched, with its Gaussian weight. -/
abbrev MatchingWeight := List ℚ × ℚ

def insertWidth (a : ℚ) : List ℚ → List ℚ
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertWidth a bs

def pairWeight (a b : ℚ) : ℚ := 2 * (min a b) ^ 2

/-- Remove one occurrence from a list, listing every labelled choice separately. -/
def eraseEach {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: as => (a, as) :: (eraseEach as).map (fun (b, rest) => (b, a :: rest))

/-- Labelled recursion for the partial matchings of Lemma 25. On the left, each successive
position is either unmatched or paired with one of the as-yet unmatched right positions. -/
def labelledMatchingWeights : List ℚ → List ℚ → List MatchingWeight
  | [], right => [(right, 1)]
  | a :: left, right =>
    ((labelledMatchingWeights left right).map fun (rest, weight) =>
      (insertWidth a rest, weight)) ++
      (eraseEach right).flatMap fun (b, remaining) =>
        (labelledMatchingWeights left remaining).map fun (rest, weight) =>
          (rest, pairWeight a b * weight)

def collectMatchingWeight (a : MatchingWeight) : List MatchingWeight → List MatchingWeight
  | [] => [a]
  | b :: bs =>
      if a.1 = b.1 then (a.1, a.2 + b.2) :: bs else a :: b :: bs

/-- Combine Gaussian weights of all terms with the same sorted unmatched widths. -/
def collectMatchingWeights (weights : List MatchingWeight) : List MatchingWeight :=
  let ordered := weights.mergeSort (fun a b => !(b.1.lex a.1 (fun x y => x < y)))
  ordered.foldr collectMatchingWeight []

/-- The recursion after grouping interchangeable right positions by width. -/
def matchingWeights : List ℚ → List ℚ → List MatchingWeight
  | [], right => [(right, 1)]
  | a :: left, right =>
    let unmatched := (matchingWeights left right).map fun (rest, weight) =>
      (insertWidth a rest, weight)
    let paired := right.dedup.flatMap fun b =>
      let factor := (right.count b : ℚ) * pairWeight a b
      (matchingWeights left (right.erase b)).map fun (rest, weight) => (rest, factor * weight)
    collectMatchingWeights (unmatched ++ paired)

/-- The contribution of the marked cumulant plus the possible exceptional unmarked block. -/
def contractionTerm (B : Primitive) (widths : List ℚ) : ℚ :=
  let marked := markedCumulant B widths
  if widths.sum ≤ 1 then marked
  else
    marked + rectangleTail widths * mean B +
      (widths.dedup.map fun a =>
        let tail := rectangleTail (widths.erase a)
        if tail = 0 then 0
        else (widths.count a : ℚ) * tail * covariance B a).sum

/-- The exact cross-matching formula applied to a convolved profile. -/
def contraction (B : Primitive) (left right : List ℚ) : ℚ :=
  (matchingWeights left (right.mergeSort (fun a b => a ≤ b))).foldl
    (fun total (rest, weight) => total + weight * contractionTerm B rest) 0

/-- Prepared rows share their spline between all Gram evaluations involving the row. -/
structure PreparedRow where
  widths : List ℚ
  coefficients : List ℚ
  weight : ℚ
  profile : Spline

def prepare (row : Rows.RowData) : PreparedRow :=
  ⟨row.widths, row.coefficients, row.weight,
    Spline.legendreProfile (1 - row.widths.sum) row.coefficients⟩

/-- Exact off-diagonal or diagonal Gram entry for a pair of prepared rows. -/
def gram (left right : PreparedRow) : ℚ :=
  let B := splinePrimitives (left.profile.convolution right.profile)
  left.weight * right.weight * contraction B left.widths right.widths

def central (row : PreparedRow) : CentralBounds :=
  centralFromSpline row.widths row.coefficients row.weight row.profile

end Chowla.Checker
