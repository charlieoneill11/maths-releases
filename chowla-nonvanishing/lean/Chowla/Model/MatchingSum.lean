import Chowla.Model.Moments

namespace Chowla

open scoped BigOperators

noncomputable def rectangleTail (A : List ℝ) : ℝ :=
  if 2 ≤ A.length then delta (A.map rectangle) else 0

noncomputable def crossMatchingSum (h : FourierProfile) (A B : List ℝ) : ℝ := by
  classical
  let widths := A ++ B
  let U : Finset (Fin widths.length) := Finset.univ
  exact ∑ P ∈ (Finset.univ : Finset (Finpartition U)).filter (fun P =>
      ∀ pair ∈ P.parts, pair.card = 1 ∨ (pair.card = 2 ∧
        (∃ i ∈ pair, i.val < A.length) ∧ (∃ i ∈ pair, A.length ≤ i.val))),
    let S := U.filter fun i => ∃ pair ∈ P.parts, pair = {i}
    let widthsIn := fun inds : Finset (Fin widths.length) =>
      (inds.sort (· ≤ ·)).map widths.get
    let marked := fun inds => cumulant (h :: (widthsIn inds).map rectangle)
    let weight := ∏ pair ∈ P.parts, if pair.card = 2 then
        2 * ((widthsIn pair).foldl min 1) ^ 2 else 1
    weight * (marked S + rectangleTail (widthsIn S) * cumulant [h] +
      ∑ i ∈ S, rectangleTail (widthsIn (S.erase i)) * cumulant [h, rectangle (widths.get i)])

end Chowla
