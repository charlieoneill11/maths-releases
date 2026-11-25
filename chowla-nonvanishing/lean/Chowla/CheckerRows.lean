import Chowla.CheckerMatching
import Chowla.CheckerTail
import Chowla.Amplitude

namespace Chowla.Checker

open MeasureTheory Set

/-- The Legendre profile of a row prior to its external rational weight. -/
noncomputable def unweightedProfile (r : Rows.RowData) : ℝ → ℝ :=
  Chowla.legendreProfile ((1 - r.widths.sum : ℚ) : ℝ)
    (r.coefficients.map fun c : ℚ => (c : ℝ))

theorem rowProfile_eq (r : Rows.RowData) :
    r.toRow.profile = fun u => (r.weight : ℝ) * unweightedProfile r u := by
  unfold unweightedProfile Rows.RowData.toRow
  rw [Rat.cast_sub, Rat.cast_one, cast_width_sum]

theorem prepared_profile_sound (r : Rows.RowData) (hr : 0 < 1 - r.widths.sum) :
    (prepare r).profile.toReal =ᵐ[volume] unweightedProfile r :=
  Spline.legendreProfile_sound _ _ hr

theorem prepared_convolution_sound (r s : Rows.RowData)
    (hr : 0 < 1 - r.widths.sum) (hs : 0 < 1 - s.widths.sum) :
    ((prepare r).profile.convolution (prepare s).profile).toReal =
      convolve (unweightedProfile r) (unweightedProfile s) := by
  rw [Spline.convolution_sound]
  exact convolve_congr (prepared_profile_sound r hr) (prepared_profile_sound s hs)

theorem prepared_central_profile_sound (r : Rows.RowData) (hr : 0 < 1 - r.widths.sum) :
    (hstarSpline.convolution (prepare r).profile).toReal =
      convolve Hstar (unweightedProfile r) := by
  rw [Spline.convolution_sound]
  exact convolve_congr hstarSpline_sound (prepared_profile_sound r hr)

/-- The rational center of the enclosure evaluates the paper's marked cumulant
with the Taylor profile Hstar and the full, weighted row. -/
theorem prepared_central_value_sound (r : Rows.RowData) (hr : 0 < 1 - r.widths.sum)
    (hη : IsProfile (unweightedProfile r))
    (hwidths : ∀ t ∈ r.widths, (t : ℝ) ∈ Ioc 0 1) :
    ((r.weight * markedCumulant
      (splinePrimitives (hstarSpline.convolution (prepare r).profile)) r.widths : ℚ) : ℝ) =
      cumulant (convolve Hstar r.toRow.profile :: r.widths.map (fun t : ℚ => rectangle (t : ℝ))) := by
  have hs := prepared_central_profile_sound r hr
  have hp : IsProfile (hstarSpline.convolution (prepare r).profile).toReal := by
    rw [hs]
    exact convolve_isProfile Hstar_isProfile hη
  rw [Rat.cast_mul, markedCumulant_sound _ _ hp hwidths, hs, rowProfile_eq]
  have he : convolve Hstar (fun u => (r.weight : ℝ) * unweightedProfile r u) =
      fun u => (r.weight : ℝ) * convolve Hstar (unweightedProfile r) u := by
    rw [convolve_comm, convolve_const_mul_head, convolve_comm (unweightedProfile r) Hstar]
  rw [he, cumulant_const_mul_head]

private theorem cast_max_neg (x : ℚ) : ((max x (-x) : ℚ) : ℝ) = |(x : ℝ)| := by
  by_cases h : 0 ≤ x
  · have hr : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
    rw [max_eq_left (by linarith), abs_of_nonneg hr]
  · have hq : x ≤ 0 := le_of_not_ge h
    have hr : (x : ℝ) ≤ 0 := by exact_mod_cast hq
    rw [max_eq_right (by linarith), Rat.cast_neg, abs_of_nonpos hr]

private theorem cast_abs_sum (cs : List ℚ) :
    ((cs.map (fun c => max c (-c))).sum : ℝ) =
      ((cs.map (fun c : ℚ => (c : ℝ))).map abs).sum := by
  induction cs with
  | nil => simp
  | cons a cs ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, cast_max_neg, ih]

private theorem cast_double_prod (A : List ℚ) :
    (((A.map (fun a : ℚ => (2 : ℚ) * a)).prod : ℚ) : ℝ) =
      ((A.map (fun a : ℚ => (a : ℝ))).map (fun a : ℝ => (2 : ℝ) * a)).prod := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.map_cons, List.prod_cons, Rat.cast_mul, Rat.cast_ofNat, ih]

theorem centralError_cast (A c : List ℚ) :
    (Checker.centralError A c : ℝ) =
      Chowla.centralError (A.map (fun a : ℚ => (a : ℝ)))
        ((1 - A.sum : ℚ) : ℝ) (c.map (fun a : ℚ => (a : ℝ))) := by
  cases A with
  | nil => simp [Checker.centralError, Chowla.centralError]
  | cons a A =>
    cases A with
    | nil =>
      simp only [Checker.centralError, Chowla.centralError, List.map_cons, List.map_nil,
        Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, cast_abs_sum]
    | cons b A =>
      have hp := cast_double_prod (a :: b :: A)
      simp only [List.map_cons] at hp
      simp only [Checker.centralError, Chowla.centralError, List.map_cons, List.length_cons,
        List.length_map, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, cast_abs_sum, hp]

private theorem convolve_const_mul_right (f g : FourierProfile) (c : ℝ) :
    convolve f (fun u => c * g u) = fun u => c * convolve f g u := by
  rw [convolve_comm, convolve_const_mul_head, convolve_comm g f]

/-- The direct rational spline evaluation encloses the central marked cumulant
with the true extremal profile for every nonempty valid row. -/
theorem prepared_central_enclosure_sound (r : Rows.RowData) (hr : 0 < 1 - r.widths.sum)
    (hne : r.widths ≠ []) (hwidths : ∀ t ∈ r.widths, (t : ℝ) ∈ Ioo 0 1) :
    let C := cumulant (convolve H r.toRow.profile :: r.widths.map
      (fun t : ℚ => rectangle (t : ℝ)))
    let b := central (prepare r)
    (b.lower : ℝ) ≤ C ∧ C ≤ (b.upper : ℝ) := by
  let A := r.widths.map fun a : ℚ => (a : ℝ)
  let c := r.coefficients.map fun a : ℚ => (a : ℝ)
  let s := ((1 - r.widths.sum : ℚ) : ℝ)
  have hA : ∀ a ∈ A, a ∈ Ioo 0 1 := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact hwidths q hq
  have hneA : A ≠ [] := by simpa [A] using hne
  have hs : 0 < s := by
    change (0 : ℝ) < ((1 - r.widths.sum : ℚ) : ℝ)
    exact_mod_cast hr
  have hη : IsProfile (unweightedProfile r) := legendreProfile_isProfile s c
  have happrox := prepared_central_value_sound r hr hη
    (fun t ht => ⟨(hwidths t ht).1, (hwidths t ht).2.le⟩)
  have herr := central_error A hA hneA c s hs
  have hev : |cumulant (convolve H r.toRow.profile :: A.map rectangle) -
        cumulant (convolve Hstar r.toRow.profile :: A.map rectangle)| ≤
      |(r.weight : ℝ)| * Chowla.centralError A s c := by
    rw [rowProfile_eq, convolve_const_mul_right, convolve_const_mul_right,
      cumulant_const_mul_head, cumulant_const_mul_head, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
  have heq : (r.widths.map fun t : ℚ => rectangle (t : ℝ)) = A.map rectangle := by
    simp [A, List.map_map, Function.comp_def]
  rw [← heq] at hev
  rw [← happrox, ← centralError_cast] at hev
  rw [Rat.cast_mul] at hev
  have habs := abs_le.mp hev
  change
    let b := centralFromSpline r.widths r.coefficients r.weight (prepare r).profile
    (b.lower : ℝ) ≤ cumulant (convolve H r.toRow.profile :: r.widths.map
      (fun t : ℚ => rectangle (t : ℝ))) ∧
      cumulant (convolve H r.toRow.profile :: r.widths.map
        (fun t : ℚ => rectangle (t : ℝ))) ≤ (b.upper : ℝ)
  unfold centralFromSpline
  have hn : r.widths.isEmpty = false := by simpa [List.isEmpty_iff] using hne
  simp only [hn, Bool.false_eq_true, if_false, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    cast_max_neg]
  constructor <;> linarith [habs.1, habs.2]

end Chowla.Checker
