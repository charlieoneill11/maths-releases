import Chowla.VariationalPointwise

namespace Chowla

open Filter
open scoped BigOperators SchwartzMap Topology

theorem nonvanishingIndicator_nonneg (d : ℤ) : 0 ≤ nonvanishingIndicator d := by
  unfold nonvanishingIndicator
  split <;> norm_num

theorem nonvanishingIndicator_le_one (d : ℤ) : nonvanishingIndicator d ≤ 1 := by
  unfold nonvanishingIndicator
  split <;> norm_num

theorem weightedSum_mono (D : DiscClass) (W : ShellWeight) (X : ℝ) {f g : ℤ → ℝ}
    (h : ∀ d ∈ classDiscs D (2 * (D.2.kappa : ℝ) * X), f d ≤ g d) :
    weightedSum D W X f ≤ weightedSum D W X g := by
  unfold weightedSum
  exact Finset.sum_le_sum fun d hd =>
    mul_le_mul_of_nonneg_left (h d hd) (W.nonnegative _)

theorem weightedMass_nonneg (D : DiscClass) (W : ShellWeight) (X : ℝ) :
    0 ≤ weightedSum D W X (fun _ => 1) := by
  unfold weightedSum
  exact Finset.sum_nonneg fun d _ => mul_nonneg (W.nonnegative _) zero_le_one

theorem weightedAverage_indicator_le_one (D : DiscClass) (W : ShellWeight) (X : ℝ) :
    weightedAverage D W X nonvanishingIndicator ≤ 1 := by
  have hnum : weightedSum D W X nonvanishingIndicator ≤ weightedSum D W X (fun _ => 1) :=
    weightedSum_mono D W X fun d _ => nonvanishingIndicator_le_one d
  by_cases hden : weightedSum D W X (fun _ => 1) = 0
  · simp [weightedAverage, hden]
  · have hpos := lt_of_le_of_ne (weightedMass_nonneg D W X) (Ne.symm hden)
    exact (div_le_iff₀ hpos).mpr (by simpa using hnum)

theorem weightedMass_pos_of_positive (D : DiscClass) (W : ShellWeight) (X : ℝ) {d : ℤ}
    (hd : d ∈ classDiscs D (2 * (D.2.kappa : ℝ) * X)) (hw : 0 < W.toFun (oddPart D d / X)) :
    0 < weightedSum D W X (fun _ => 1) := by
  unfold weightedSum
  refine lt_of_lt_of_le (show 0 < W.toFun (oddPart D d / X) * (1 : ℝ) by simpa using hw) ?_
  exact Finset.single_le_sum (f := fun a => W.toFun (oddPart D a / X) * (1 : ℝ))
    (fun a _ => mul_nonneg (W.nonnegative _) zero_le_one) hd

/-- Weighted passage from the pointwise bound to the averaged vanishing indicator. -/
theorem weighted_pointwise_bound (D : DiscClass) (W : ShellWeight) (X : ℝ) (N : ℤ → ℝ)
    (hmass : 0 < weightedSum D W X (fun _ => 1))
    (hb : ∀ d ∈ classDiscs D (2 * (D.2.kappa : ℝ) * X),
      2 * (1 - nonvanishingIndicator d) ≤ N d) :
    2 * (1 - weightedAverage D W X nonvanishingIndicator) ≤ weightedAverage D W X N := by
  have hsum := weightedSum_mono D W X hb
  have hs : weightedSum D W X (fun d => 2 * (1 - nonvanishingIndicator d)) =
      2 * (weightedSum D W X (fun _ => 1) - weightedSum D W X nonvanishingIndicator) := by
    simp only [weightedSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [hs] at hsum
  change 2 * (1 - weightedSum D W X nonvanishingIndicator /
    weightedSum D W X (fun _ => 1)) ≤ weightedSum D W X N / weightedSum D W X (fun _ => 1)
  apply (le_div_iff₀ hmass).mpr
  calc
    _ = 2 * (weightedSum D W X (fun _ => 1) - weightedSum D W X nonvanishingIndicator) := by
      field_simp
    _ ≤ _ := hsum

/-- A limit for the mean sum of squares gives an eventual lower bound on nonvanishing. -/
theorem weighted_nonvanishing_of_limit (D : DiscClass) (W : ShellWeight) (N : ℝ → ℤ → ℝ)
    (Q ε : ℝ) (hε : 0 < ε)
    (hmass : ∀ᶠ X in atTop, 0 < weightedSum D W X (fun _ => 1))
    (hb : ∀ᶠ X in atTop, ∀ d ∈ classDiscs D (2 * (D.2.kappa : ℝ) * X),
      2 * (1 - nonvanishingIndicator d) ≤ N X d)
    (hlim : Tendsto (fun X => weightedAverage D W X (N X)) atTop (𝓝 Q)) :
    ∀ᶠ X in atTop,
      1 - Q / 2 - ε ≤ weightedAverage D W X nonvanishingIndicator := by
  have hupper : ∀ᶠ X in atTop, weightedAverage D W X (N X) < Q + 2 * ε :=
    hlim.eventually (Iio_mem_nhds (show Q < Q + 2 * ε by linarith))
  filter_upwards [hmass, hb, hupper] with X hXm hXb hXu
  have hX := weighted_pointwise_bound D W X (N X) hXm hXb
  linarith only [hX, hXu]

/-- The decay bound in the paper for real Schwartz functions. -/
theorem schwartz_decay (f : 𝓢(ℝ, ℝ)) :
    ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C / (1 + x^2) := by
  let A := SchwartzMap.seminorm ℝ 0 0 f
  let B := SchwartzMap.seminorm ℝ 2 0 f
  refine ⟨A + B, fun x => (le_div_iff₀ (by positivity : 0 < 1 + x^2)).mpr ?_⟩
  have hA : |f x| ≤ A := by simpa [A, Real.norm_eq_abs] using f.norm_le_seminorm ℝ x
  have hB : x^2 * |f x| ≤ B := by
    simpa [B, Real.norm_eq_abs, sq_abs] using f.norm_pow_mul_le_seminorm ℝ 2 x
  nlinarith only [hA, hB]

/-- A real Schwartz function gives an absolutely summable series of squared zero values. -/
theorem summable_sq_schwartz (c : CitedFacts) (d : ℤ) (X : ℝ) (A : 𝓢(ℝ, ℝ))
    (hd : IsFundDisc d) (hd' : 1 < |d|) (hX : 1 < X) :
    Summable (fun z : ZeroCopy d => (zeroSummand A d X z)^2) := by
  obtain ⟨C, hC⟩ := schwartz_decay A
  have hCn : 0 ≤ C := by
    have h := hC 0
    simp at h
    exact le_trans (abs_nonneg _) h
  have hf : ∀ x, |A x ^ 2| ≤ C ^ 2 / (1 + x^2) := by
    intro x
    have hden : 1 ≤ 1 + x^2 := by linarith [sq_nonneg x]
    have hAx : |A x| ≤ C :=
      (hC x).trans (div_le_self hCn hden)
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc
      |A x| ^ 2 ≤ C * |A x| := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right hAx (abs_nonneg _)
      _ ≤ C * (C / (1 + x^2)) := mul_le_mul_of_nonneg_left (hC x) hCn
      _ = _ := by ring
  exact zeroStatistic_summable c (fun x => A x ^ 2) d X hd hd' hX ⟨C ^ 2, hf⟩

end Chowla
