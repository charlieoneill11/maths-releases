import Chowla.EnclosureProofs
import Chowla.RowBounds
import Chowla.SplineLegendre

namespace Chowla

open Filter MeasureTheory Set
open scoped Topology

private theorem continuous_legendrePair (n : ℕ) :
    Continuous (fun x : ℝ => legendrePair x n) := by
  induction n with
  | zero =>
      change Continuous (fun x : ℝ => ((1 : ℝ), x))
      exact continuous_const.prodMk continuous_id
  | succ n ih =>
      change Continuous (fun x : ℝ => ((legendrePair x n).2,
        ((2 * (n : ℝ) + 3) * x * (legendrePair x n).2 -
          ((n : ℝ) + 1) * (legendrePair x n).1) / ((n : ℝ) + 2)))
      exact ih.snd.prodMk
        ((((continuous_const.mul continuous_id).mul ih.snd).sub
          (continuous_const.mul ih.fst)).div_const _)

private theorem legendrePair_parity (n : ℕ) (x : ℝ) :
    (legendrePair (-x) n).1 = (-1 : ℝ)^n * (legendrePair x n).1 ∧
      (legendrePair (-x) n).2 = (-1 : ℝ)^(n+1) * (legendrePair x n).2 := by
  induction n with
  | zero => simp [legendrePair]
  | succ n ih =>
      refine ⟨ih.2, ?_⟩
      change ((2 * (n : ℝ) + 3) * (-x) * (legendrePair (-x) n).2 -
        ((n : ℝ) + 1) * (legendrePair (-x) n).1) / ((n : ℝ) + 2) =
          (-1 : ℝ)^(n+1+1) *
            (((2 * (n : ℝ) + 3) * x * (legendrePair x n).2 -
              ((n : ℝ) + 1) * (legendrePair x n).1) / ((n : ℝ) + 2))
      rw [ih.1, ih.2]
      simp only [pow_succ, div_eq_mul_inv]
      ring

private theorem legendreProfile_term_even (n : ℕ) :
    Function.Even (legendre (2 * n)) := by
  intro x
  simpa [legendre, pow_mul] using (legendrePair_parity (2 * n) x).1

theorem legendreProfile_isProfile (s : ℝ) (c : List ℝ) :
    IsProfile (legendreProfile s c) := by
  unfold legendreProfile
  apply IsProfile.of_even_continuous_truncate
  · intro u
    simp only [neg_div, legendreProfile_term_even _ (u / s)]
  · apply continuous_finset_sum
    intro j _
    exact continuous_const.mul <| (continuous_legendrePair _).fst.comp
      (continuous_id.div_const s)

theorem legendreProfile_hasRadiusAtMost {s : ℝ} (hs : 0 ≤ s) (c : List ℝ) :
    HasRadiusAtMost (legendreProfile s c) s := by
  refine ⟨hs, Eventually.of_forall fun u hu => ?_⟩
  simp [legendreProfile, hu]

theorem profileL1_legendreProfile_le_of_bound {s C : ℝ} (hs : 0 ≤ s)
    (c : List ℝ) (hbound : ∀ u, |legendreProfile s c u| ≤ C) :
    profileL1 (legendreProfile s c) ≤ 2 * s * C := by
  let I := Set.Icc (-s) s
  have hI : MeasurableSet I := measurableSet_Icc
  have hInt : Integrable (I.indicator fun _ => C) :=
    (integrable_indicator_iff hI).2 (integrableOn_const isCompact_Icc.measure_ne_top)
  calc
    profileL1 (legendreProfile s c) ≤ ∫ u : ℝ, I.indicator (fun _ => C) u := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hInt
      filter_upwards with u
      by_cases hu : u ∈ I
      · rw [Set.indicator_of_mem hu]
        exact hbound u
      · simp [I, legendreProfile, Set.indicator_of_notMem hu]
    _ = _ := by
      rw [integral_indicator hI, setIntegral_const, Real.volume_real_Icc]
      change max (s - -s) 0 * C = 2 * s * C
      rw [max_eq_left (by linarith)]
      ring

theorem IsProfile.const_mul {h : FourierProfile} (hh : IsProfile h) (c : ℝ) :
    IsProfile (fun u => c * h u) := by
  refine ⟨measurable_const.mul hh.1, fun u => congrArg (c * ·) (hh.2.1 u), ?_, ?_⟩
  · obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hh.2.2.1
    refine isBounded_iff_forall_norm_le.mpr ⟨|c| * B, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hB _ ⟨u, rfl⟩)
      (abs_nonneg _)
  · apply HasCompactSupport.of_support_subset_isCompact hh.2.2.2.isCompact
    intro u hu
    apply subset_closure
    exact fun hzero => hu (by simp [hzero])

theorem HasRadiusAtMost.const_mul {h : FourierProfile} {s : ℝ}
    (hh : HasRadiusAtMost h s) (c : ℝ) : HasRadiusAtMost (fun u => c * h u) s := by
  refine ⟨hh.1, ?_⟩
  filter_upwards [hh.2] with u h hu
  simp [h hu]

theorem Rows.RowData.toRow_admissible_of_widths (r : Rows.RowData)
    (hw : ∀ a ∈ r.toRow.widths, a ∈ Set.Ioo (0 : ℝ) 1)
    (hs : r.toRow.widths.sum < 1) : r.toRow.Admissible := by
  let s := 1 - r.toRow.widths.sum
  let c : List ℝ := r.coefficients.map (↑)
  have hspos : 0 < s := sub_pos.mpr hs
  have hp := legendreProfile_isProfile s c
  have hc := legendreProfile_hasRadiusAtMost hspos.le c
  refine ⟨hw, hp.const_mul _, ?_, radius_le_of_hasRadiusAtMost (hc.const_mul _)⟩
  change (∫ u : ℝ, (r.weight : ℝ) * legendreProfile s c u) = 0
  rw [integral_const_mul, legendreProfile_integral s hspos c, mul_zero]

/-- The concrete final amplitude satisfies Definition 20. -/
theorem final_amplitude_admissible : IsAmplitude F₈ := by
  intro k hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
  obtain ⟨hwidths, hs⟩ := finalRows_validWidths r hr
  exact r.toRow_admissible_of_widths hwidths hs

noncomputable def centralError (A : List ℝ) (s : ℝ) (c : List ℝ) : ℝ :=
  match A with
  | [] => 0
  | [a] => 8 * a^2 * s * (c.map abs).sum / (10 : ℝ)^12
  | _ => 2^A.length * (2 / (10 : ℝ)^12) * (2 * s * (c.map abs).sum) *
      (A.map (fun a => 2*a)).prod

private theorem profileL1_legendreProfile_le (s : ℝ) (hs : 0 < s) (c : List ℝ) :
    profileL1 (legendreProfile s c) ≤ 2 * s * (c.map abs).sum :=
  profileL1_legendreProfile_le_of_bound hs.le c (legendreProfile_bound s hs c)

/-- Lemma 30, the exact central error used in the rational enclosures. -/
theorem central_error (A : List ℝ)
    (hA : ∀ a ∈ A, a ∈ Set.Ioo (0 : ℝ) 1) (hne : A ≠ [])
    (c : List ℝ) (s : ℝ) (hspos : 0 < s) :
    |cumulant (convolve H (legendreProfile s c) :: A.map rectangle) -
      cumulant (convolve Hstar (legendreProfile s c) :: A.map rectangle)| ≤
      centralError A s c := by
  have hη := legendreProfile_isProfile s c
  have hl := profileL1_legendreProfile_le s hspos c
  obtain _ | ⟨a, A⟩ := A
  · exact (hne rfl).elim
  cases A with
  | nil =>
    have ha := hA a (by simp)
    have hs := central_error_single hη ⟨ha.1, ha.2.le⟩
    simp only [List.map_cons, List.map_nil, centralError]
    refine hs.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (by positivity)) (by positivity)).trans_eq ?_)
    ring
  | cons b rest =>
    have hn : ∀ x ∈ a :: b :: rest, 0 ≤ x := fun x hx => (hA x hx).1.le
    let A := a :: b :: rest
    have h := central_error_higher H_isProfile hη A (by simp [A]) hn
    change _ ≤ (2 : ℝ)^A.length * (2 / (10 : ℝ)^12) * (2 * s * (c.map abs).sum) *
      (A.map fun x => 2*x).prod
    have hAp : 0 ≤ (A.map fun x => 2*x).prod := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact mul_nonneg (by norm_num) (hn t ht)
    refine h.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (by positivity)) hAp


end Chowla
