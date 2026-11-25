import LeastPrime.DivisorReduction
import LeastPrime.SizeBiasedSupport
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Transfer of the cited limiting law to dyadic divisor counts. -/

namespace LeastPrime

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The Donnelly–Grimmett field, isolated for the divisor-density theorems. -/
def DonnellyGrimmettInput : Prop :=
  ∀ j : ℕ, 0 < j → Tendsto (averageLaw j) atTop (𝓝 (stickProbability j))

private theorem weightedMixture_real {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (laws : ι → ProbabilityMeasure Ω) (S : Set Ω) :
    (weightedMixture w hw laws : Measure Ω).real S =
      ∑ i, (w i / ∑ k, w k) * ((laws i : Measure Ω).real S) := by
  have htotal : 0 < ∑ i, w i :=
    Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  simp only [measureReal_def, weightedMixture_apply]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (hw _).le htotal.le)]

private theorem sum_fin_Ioc {M : Type*} [AddCommMonoid M] (X : ℕ) (f : ℕ → M) :
    (∑ i : Fin X, f (i.val + 1)) = ∑ n ∈ Finset.Ioc 0 X, f n := by
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1))]
  induction X with
  | zero => simp
  | succ X ih =>
    have hioc : insert (X + 1) (Finset.Ioc 0 X) = Finset.Ioc 0 (X + 1) := by
      ext n
      simp only [Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [Finset.sum_range_succ, ih, ← hioc, Finset.sum_insert (by simp)]
    exact add_comm _ _

private theorem sum_averageLaw (j X : ℕ) (A : Set (Fin j → ℝ)) :
    (X : ℝ) * (averageLaw j X : Measure (Fin j → ℝ)).real A =
      ∑ n ∈ Finset.Ioc 0 X, (sizeBiasedLaw j n : Measure (Fin j → ℝ)).real A := by
  cases X with
  | zero => simp
  | succ X =>
    rw [averageLaw, weightedMixture_real]
    have hsum : ∑ _ : Fin (X + 1), (1 : ℝ) = ((X + 1 : ℕ) : ℝ) := by simp
    rw [hsum, ← Finset.mul_sum, ← mul_assoc]
    rw [show (↑(X + 1) : ℝ) * (1 / (↑(X + 1) : ℝ)) = 1 from by
      rw [mul_one_div_cancel (by positivity)], one_mul]
    exact sum_fin_Ioc (X + 1) (fun n => (sizeBiasedLaw j n : Measure (Fin j → ℝ)).real A)

private theorem window_sum_eq_sub {M : Type*} [AddCommGroup M] (f : ℕ → M) {Q : ℝ} (hQ : 0 ≤ Q) :
    (∑ n ∈ window Q, f n) =
      (∑ n ∈ Finset.Ioc 0 ⌊Q⌋₊, f n) - ∑ n ∈ Finset.Ioc 0 ⌊Q / 2⌋₊, f n := by
  have hY : ⌊Q / 2⌋₊ ≤ ⌊Q⌋₊ := Nat.floor_mono (by linarith)
  have hsub : Finset.Ioc 0 ⌊Q / 2⌋₊ ⊆ Finset.Ioc 0 ⌊Q⌋₊ := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans hY⟩
  have hdiff : Finset.Ioc 0 ⌊Q⌋₊ \ Finset.Ioc 0 ⌊Q / 2⌋₊ = window Q := by
    rw [window_eq_Ioc hQ]
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  have hs := Finset.sum_sdiff (f := f) hsub
  rw [hdiff] at hs
  exact eq_sub_of_add_eq hs

private theorem floor_half_ratio :
    Tendsto (fun Q : ℝ => (⌊Q / 2⌋₊ : ℝ) / Q) atTop (𝓝 (1 / 2)) := by
  simpa only [show ∀ Q : ℝ, (1 / 2 : ℝ) * Q = Q / 2 by intro Q; ring] using
    (tendsto_nat_floor_mul_div_atTop (a := (1 / 2 : ℝ)) (by norm_num))

/-- The fraction of integers up to `Q` lying in the dyadic window tends to one half. -/
theorem window_card_ratio :
    Tendsto (fun Q : ℝ => ((window Q).card : ℝ) / Q) atTop (𝓝 (1 / 2)) := by
  have h : Tendsto (fun Q : ℝ => (⌊Q⌋₊ : ℝ) / Q - (⌊Q / 2⌋₊ : ℝ) / Q)
      atTop (𝓝 (1 - 1 / 2)) :=
    tendsto_nat_floor_div_atTop.sub floor_half_ratio
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with Q hQ
  have hY : ⌊Q / 2⌋₊ ≤ ⌊Q⌋₊ := Nat.floor_mono (by linarith)
  rw [window_card hQ, Nat.cast_sub hY, sub_div]

private def windowMeasureSum (j : ℕ) (A : Set (Fin j → ℝ)) (Q : ℝ) : ℝ :=
  ∑ n ∈ window Q, (sizeBiasedLaw j n : Measure (Fin j → ℝ)).real A

private theorem dyadic_measure_limit (hDG : DonnellyGrimmettInput) {j : ℕ} (hj : 0 < j)
    {A : Set (Fin j → ℝ)} (hA : stickLaw j (frontier A) = 0) :
    Tendsto (fun Q : ℝ => windowMeasureSum j A Q / Q) atTop
      (𝓝 ((stickLaw j).real A / 2)) := by
  have key : Tendsto (fun X : ℕ => (averageLaw j X : Measure (Fin j → ℝ)).real A) atTop
      (𝓝 ((stickLaw j).real A)) := by
    have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (hDG j hj) hA
    exact (ENNReal.tendsto_toReal (measure_ne_top (stickLaw j) A)).comp h
  have hY : Tendsto (fun Q : ℝ => ⌊Q / 2⌋₊) atTop atTop := by
    simpa only [show ∀ Q : ℝ, (1 / 2 : ℝ) * Q = Q / 2 by intro Q; ring,
      Function.comp_apply] using
      (tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)))
  have hx := key.comp (tendsto_nat_floor_atTop : Tendsto (fun Q : ℝ => ⌊Q⌋₊) atTop atTop)
  have hy := key.comp hY
  have h := (tendsto_nat_floor_div_atTop.mul hx).sub (floor_half_ratio.mul hy)
  rw [show (1 : ℝ) * (stickLaw j).real A - (1 / 2) * (stickLaw j).real A =
    (stickLaw j).real A / 2 by ring] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with Q hQ
  simp only [Function.comp_apply, windowMeasureSum]
  rw [window_sum_eq_sub _ hQ, ← sum_averageLaw, ← sum_averageLaw]
  ring

private theorem sum_indicator_eq_windowCount (Q : ℝ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ n ∈ window Q, if P n then (1 : ℝ) else 0) = (windowCount Q P : ℝ) := by
  unfold windowCount
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  rw [Finset.filter_congr_decidable (window Q) P (fun _ => Classical.propDecidable _)]

/-- The lower half of the transfer, stated for any measurable continuity set of inner
witnesses. -/
theorem eventually_density_lower_of_nullFrontier (hDG : DonnellyGrimmettInput)
    {j : ℕ} (hj : 0 < j) {T : Set ℝ} (hE : MeasurableSet (E j T))
    (hfront : stickLaw j (frontier (E j T)) = 0) {a : ℝ} (ha : a < p j T) :
    ∀ᶠ Q in atTop, a * (window Q).card < windowCount Q (fun n => HasLogDivisorIn n T) := by
  classical
  have hlim := (dyadic_measure_limit hDG hj hfront).sub (window_card_ratio.const_mul a)
  have ht : 0 < (stickLaw j).real (E j T) / 2 - a * (1 / 2) := by
    change a < (stickLaw j).real (E j T) at ha
    linarith
  filter_upwards [hlim.eventually_const_lt ht, eventually_gt_atTop (2 : ℝ)] with Q hQ hQ₂
  have hQpos : 0 < Q := by linarith
  have hsum : windowMeasureSum j (E j T) Q ≤
      (windowCount Q (fun n => HasLogDivisorIn n T) : ℝ) := by
    rw [← sum_indicator_eq_windowCount]
    exact Finset.sum_le_sum fun n hn => sizeBiasedLaw_real_E_le_indicator (window_mem_two_le hQ₂ hn) hE
  apply lt_of_lt_of_le _ hsum
  apply (div_lt_div_iff_of_pos_right hQpos).mp
  change 0 < windowMeasureSum j (E j T) Q / Q - a * ((window Q).card / Q) at hQ
  rw [mul_div_assoc]
  linarith

/-- The upper half of the transfer for a measurable continuity set of outer witnesses. -/
theorem eventually_density_upper_of_nullFrontier (hDG : DonnellyGrimmettInput)
    {j : ℕ} (hj : 0 < j) {T : Set ℝ} (hF : MeasurableSet (F j T))
    (hfront : stickLaw j (frontier (F j T)) = 0) {b : ℝ} (hb : q j T < b) :
    ∀ᶠ Q in atTop, (windowCount Q (fun n => HasLogDivisorIn n T) : ℝ) < b * (window Q).card := by
  classical
  have hlim := (window_card_ratio.const_mul b).sub (dyadic_measure_limit hDG hj hfront)
  have ht : 0 < b * (1 / 2) - (stickLaw j).real (F j T) / 2 := by
    change (stickLaw j).real (F j T) < b at hb
    linarith
  filter_upwards [hlim.eventually_const_lt ht, eventually_gt_atTop (2 : ℝ)] with Q hQ hQ₂
  have hQpos : 0 < Q := by linarith
  have hsum : (windowCount Q (fun n => HasLogDivisorIn n T) : ℝ) ≤
      windowMeasureSum j (F j T) Q := by
    rw [← sum_indicator_eq_windowCount]
    exact Finset.sum_le_sum fun n hn => indicator_le_sizeBiasedLaw_real_F (window_mem_two_le hQ₂ hn) hF
  apply lt_of_le_of_lt hsum
  apply (div_lt_div_iff_of_pos_right hQpos).mp
  change 0 < b * ((window Q).card / Q) - windowMeasureSum j (F j T) Q / Q at hQ
  rw [mul_div_assoc]
  linarith

end

end LeastPrime
