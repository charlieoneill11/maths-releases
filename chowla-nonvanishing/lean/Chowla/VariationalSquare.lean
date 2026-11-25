import Chowla.VariationalWick

namespace Chowla

open Filter MeasureTheory MvPolynomial
open scoped BigOperators Convolution SchwartzMap Topology

/-- A Schwartz test constructed from a smooth, compact Fourier profile. -/
structure SmoothProfile where
  profile : FourierProfile
  isProfile : IsProfile profile
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) profile

noncomputable def SmoothProfile.test (h : SmoothProfile) : MomentTest :=
  MomentTest.ofProfile h.profile h.isProfile h.smooth

@[simp] theorem SmoothProfile.test_profile (h : SmoothProfile) : h.test.profile = h.profile :=
  MomentTest.ofProfile_profile _ _ _

noncomputable def SmoothProfile.mul (h g : SmoothProfile) : SmoothProfile where
  profile := convolve h.profile g.profile
  isProfile := convolve_isProfile h.isProfile g.isProfile
  smooth := g.isProfile.2.2.2.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (integrable_of_isProfile h.isProfile).locallyIntegrable g.smooth

theorem SmoothProfile.mul_test_apply (h g : SmoothProfile) (x : ℝ) :
    (h.mul g).test.toSchwartz x = h.test.toSchwartz x * g.test.toSchwartz x := by
  simp only [SmoothProfile.test, MomentTest.ofProfile_apply, SmoothProfile.mul]
  exact inverseProfile_convolve _ _ h.isProfile g.isProfile h.smooth.continuous g.smooth.continuous _

theorem SmoothProfile.mul_radius (h g : SmoothProfile) :
    radius (h.mul g).test.profile ≤ radius h.profile + radius g.profile := by
  simpa only [SmoothProfile.test_profile] using radius_convolve_le h.isProfile g.isProfile

section Square

variable {ι : Type*} (I : Finset ι) (a : ι → ℝ) (h : ι → SmoothProfile) (T : ι → List MomentTest)

/-- The polynomial in zero statistics obtained by expanding the square of the test amplitude. -/
noncomputable def squarePolynomial : MomentPolynomial :=
  MomentPolynomial.sum (I.toList.map fun i => MomentPolynomial.sum (I.toList.map fun j =>
    MomentPolynomial.mul
      (MomentPolynomial.mul (MomentPolynomial.const (a i * a j))
        (MomentPolynomial.atom ((h i).mul (h j)).test))
      (MomentPolynomial.mul (wickPolynomial (T i)) (wickPolynomial (T j)))))

theorem squarePolynomial_model : (squarePolynomial I a h T).model =
    ∑ i ∈ I, ∑ j ∈ I, C (a i * a j) * stat (convolve (h i).profile (h j).profile) *
      (wick ((T i).map MomentTest.profile) * wick ((T j).map MomentTest.profile)) := by
  rw [← MomentPolynomial.eval_model]
  unfold squarePolynomial
  simp only [MomentPolynomial.eval_sum, List.map_map, Function.comp_def, Finset.sum_map_toList,
    MomentPolynomial.eval_mul, MomentPolynomial.eval_const, MomentPolynomial.eval_atom,
    SmoothProfile.test_profile, SmoothProfile.mul, MomentPolynomial.eval_model, wickPolynomial_model]

theorem squarePolynomial_statistic (X : ℝ) (d : ℤ) : (squarePolynomial I a h T).statistic X d =
    ∑ i ∈ I, ∑ j ∈ I, (a i * a j) *
      zeroStatistic (fun x => (((h i).mul (h j)).test.toSchwartz) x) d X *
      (wickStatistic (T i) X d * wickStatistic (T j) X d) := by
  rw [← MomentPolynomial.eval_real]
  unfold squarePolynomial
  simp only [MomentPolynomial.eval_sum, List.map_map, Function.comp_def, Finset.sum_map_toList,
    MomentPolynomial.eval_mul, MomentPolynomial.eval_const, MomentPolynomial.eval_atom,
    RingHom.id_apply, MomentPolynomial.eval_real, wickStatistic]

theorem squarePolynomial_bandwidth
    (hb : ∀ i ∈ I, ∀ j ∈ I, radius (h i).profile + radius (h j).profile +
      (MomentWord.bandwidth (T i) + MomentWord.bandwidth (T j)) < 2) :
    ∀ t ∈ squarePolynomial I a h T, t.2 ≠ [] ∧ MomentWord.bandwidth t.2 < 2 := by
  intro t ht
  unfold squarePolynomial MomentPolynomial.sum at ht
  obtain ⟨p, hp, ht⟩ := List.mem_flatten.mp ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  obtain ⟨q, hq, ht⟩ := List.mem_flatten.mp ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  obtain ⟨v, hv, w, hw, rfl⟩ := MomentPolynomial.mem_mul ht
  obtain ⟨v', hv', f, hf, rfl⟩ := MomentPolynomial.mem_mul hv
  simp only [MomentPolynomial.const, List.mem_singleton] at hv'
  simp only [MomentPolynomial.atom, List.mem_singleton] at hf
  subst v' f
  refine ⟨by simp, ?_⟩
  have he := MomentPolynomial.bandwidth_mul (wickPolynomial_bandwidth (T i))
    (wickPolynomial_bandwidth (T j)) w hw
  have hwidth := SmoothProfile.mul_radius (h i) (h j)
  have hbound := hb i (Finset.mem_toList.mp hi) j (Finset.mem_toList.mp hj)
  simp only [List.nil_append, MomentWord.bandwidth, List.cons_append, List.map_cons, List.sum_cons]
  change radius ((h i).mul (h j)).test.profile + MomentWord.bandwidth w.2 < 2
  linarith only [hwidth, he, hbound]

/-- As a function of the ordinate of a zero, a test amplitude is Schwartz. -/
noncomputable def numericalAmplitude (X : ℝ) (d : ℤ) : 𝓢(ℝ, ℝ) :=
  ∑ i ∈ I, (a i * wickStatistic (T i) X d) • (h i).test.toSchwartz

theorem numericalAmplitude_zero {X : ℝ} {d : ℤ}
    (hzero : ∑ i ∈ I, a i * wickStatistic (T i) X d * (∫ u : ℝ, (h i).profile u) = 1) :
    numericalAmplitude I a h T X d 0 = 1 := by
  simpa only [numericalAmplitude, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul,
    SmoothProfile.test, MomentTest.ofProfile_apply, inverseProfile_zero (h _).isProfile] using hzero

/-- Expansion of the pointwise sum of squares, including the interchange of zero and row sums. -/
theorem squarePolynomial_eq_zeroStatistic (c : CitedFacts) {d : ℤ} {X : ℝ}
    (hd : IsFundDisc d) (hd' : 1 < |d|) (hX : 1 < X) :
    (squarePolynomial I a h T).statistic X d =
      zeroStatistic (fun x => (numericalAmplitude I a h T X d x)^2) d X := by
  classical
  let w := fun i => a i * wickStatistic (T i) X d
  let f := fun i j z => zeroSummand (((h i).mul (h j)).test.toSchwartz) d X z
  have hs (i j : ι) : Summable (f i j) := zeroStatistic_summable c _ _ _ hd hd' hX
    (schwartz_decay ((h i).mul (h j)).test.toSchwartz)
  have ht (i : ι) : Summable (fun z => ∑ j ∈ I, (w i * w j) * f i j z) := by
    apply summable_sum fun j _ => (hs i j).mul_left _
  have hsq (z : ZeroCopy d) : zeroSummand (fun x => (numericalAmplitude I a h T X d x)^2) d X z =
      ∑ i ∈ I, ∑ j ∈ I, (w i * w j) * f i j z := by
    simp only [zeroSummand, numericalAmplitude, SchwartzMap.sum_apply, SchwartzMap.smul_apply,
      smul_eq_mul, pow_two, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [w, f, zeroSummand, SmoothProfile.mul_test_apply]
    ring
  rw [zeroStatistic, tsum_congr hsq, Summable.tsum_finsetSum (fun i _ => ht i)]
  rw [squarePolynomial_statistic]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum (fun j _ => (hs i j).mul_left _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]
  unfold w f zeroStatistic
  ring

/-- The smoothed variational bound, at fixed smoothing parameters. -/
theorem weighted_nonvanishing_of_square (c : CitedFacts)
    (m : PaperClaims) (D : DiscClass) (W : ShellWeight) (ε : ℝ) (hε : 0 < ε)
    (hmass : ∀ᶠ X in atTop, 0 < weightedSum D W X (fun _ => 1))
    (hb : ∀ i ∈ I, ∀ j ∈ I, radius (h i).profile + radius (h j).profile +
      (MomentWord.bandwidth (T i) + MomentWord.bandwidth (T j)) < 2)
    (hzero : ∀ X d, ∑ i ∈ I, a i * wickStatistic (T i) X d * (∫ u : ℝ, (h i).profile u) = 1) :
    ∀ᶠ X in atTop,
      1 - modelExpectation (squarePolynomial I a h T).model / 2 - ε ≤
        weightedAverage D W X nonvanishingIndicator := by
  apply weighted_nonvanishing_of_limit D W (squarePolynomial I a h T).statistic _ ε hε hmass _
    (momentPolynomial_limit m D W _ (squarePolynomial_bandwidth I a h T hb))
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX d hd
  simp only [classDiscs, discs, Finset.mem_filter] at hd
  obtain ⟨hf, hd'⟩ := hd.1.2
  rw [squarePolynomial_eq_zeroStatistic I a h T c hf hd' hX]
  exact pointwise_vanishing_bound c _ _ _ hf hd'
    (numericalAmplitude_zero I a h T (hzero X d)) (summable_sq_schwartz c d X _ hf hd' hX)

end Square

end Chowla
