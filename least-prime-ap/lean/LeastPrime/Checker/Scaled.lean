import LeastPrime.Checker.Grid
import LeastPrime.Checker.Quadrature

/-! Directed rounding and inclusion for residual targets. -/

namespace LeastPrime.Checker

open Set

noncomputable section

private theorem grid_quota_lower (n : Nat) {d : Nat} :
    grid (quotient .lower (n * unit) d) ≤ grid n / grid d := by
  apply (div_le_iff₀ unit_real_pos).mpr
  calc
    (quotient .lower (n * unit) d : ℝ) ≤ ((n * unit : Nat) : ℝ) / d :=
      quotient_lower_le (n * unit) d
    _ = (grid n / grid d) * (unit : ℝ) := by
      simp only [grid, div_div_div_cancel_right₀ unit_real_pos.ne', Nat.cast_mul]
      ring

private theorem grid_quota_upper (n : Nat) {d : Nat} (hd : 0 < d) :
    grid n / grid d ≤ grid (quotient .upper (n * unit) d) := by
  apply (le_div_iff₀ unit_real_pos).mpr
  calc
    (grid n / grid d) * (unit : ℝ) = ((n * unit : Nat) : ℝ) / d := by
      simp only [grid, div_div_div_cancel_right₀ unit_real_pos.ne', Nat.cast_mul]
      ring
    _ ≤ (quotient .upper (n * unit) d : ℝ) := le_quotient_upper hd

private theorem quotient_le_unit (bound : Bound) {n d : Nat} (hd : 0 < d) (hnd : n ≤ d) :
    quotient bound (n * unit) d ≤ unit := by
  have hmul : n * unit ≤ unit * d := by
    rw [Nat.mul_comm unit d]
    exact Nat.mul_le_mul_right unit hnd
  cases bound
  · apply Nat.lt_succ_iff.mp
    rw [quotient, Nat.div_lt_iff_lt_mul hd, Nat.succ_mul]
    omega
  · apply Nat.lt_succ_iff.mp
    rw [quotient, Nat.div_lt_iff_lt_mul hd, Nat.succ_mul]
    omega

private theorem keep_lower (I : GridInterval) :
    keepInterval .lower I = true ↔ I.1 < I.2 := by
  simp [keepInterval]

private theorem keep_upper (I : GridInterval) :
    keepInterval .upper I = true ↔ I.1 ≤ I.2 := by
  simp [keepInterval]

private theorem scaledInterval_good (bound : Bound) {a b : Nat} {I : GridInterval}
    (ha : 0 < a) (hab : a ≤ b) (hbelow : I.2 ≤ a)
    (hkeep : keepInterval bound (scaledInterval bound a b I) = true) :
    Good (scaledInterval bound a b I) := by
  cases bound
  · exact ⟨(keep_lower _).mp hkeep |>.le, quotient_le_unit .lower (ha.trans_le hab) (hbelow.trans hab)⟩
  · exact ⟨(keep_upper _).mp hkeep, quotient_le_unit .upper ha hbelow⟩

private theorem scaledUpper_kept {a b : Nat} {I : GridInterval}
    (ha : 0 < a) (hab : a ≤ b) (hI : Good I) :
    keepInterval .upper (scaledInterval .upper a b I) = true := by
  rw [keep_upper, ← grid_le_iff]
  have ha' : 0 < grid a := by rw [← grid_zero, grid_lt_iff]; exact ha
  have hlo := grid_quota_lower I.1 (d := b)
  have hhi := grid_quota_upper I.2 ha
  change grid (quotient .lower (I.1 * unit) b) ≤ grid (quotient .upper (I.2 * unit) a)
  apply hlo.trans (le_trans _ hhi)
  exact (div_le_div_of_nonneg_left (grid_nonneg I.1) ha' (grid_le_iff.mpr hab)).trans
    (div_le_div_of_nonneg_right (grid_le_iff.mpr hI.1) ha'.le)

private theorem mem_roundedIntervals {bound : Bound} {below : GridSet} {a b : Nat}
    {J : GridInterval} :
    J ∈ roundedIntervals bound below a b ↔
      ∃ I ∈ below, keepInterval bound (scaledInterval bound a b I) = true ∧
        (J = scaledInterval bound a b I ∨ J = reflectInterval (scaledInterval bound a b I)) := by
  rw [roundedIntervals, List.mem_flatMap]
  apply exists_congr
  intro I
  by_cases h : keepInterval bound (scaledInterval bound a b I) = true <;> simp [h]

private theorem roundedIntervals_good {bound : Bound} {below : GridSet} {a b : Nat}
    (ha : 0 < a) (hab : a ≤ b) (_hI : ∀ I ∈ below, Good I) (hbelow : ∀ I ∈ below, I.2 ≤ a) :
    ∀ J ∈ roundedIntervals bound below a b, Good J := by
  intro J hj
  obtain ⟨I, hi, hk, hr⟩ := mem_roundedIntervals.mp hj
  have hg := scaledInterval_good bound ha hab (hbelow I hi) hk
  rcases hr with rfl | rfl
  · exact hg
  · exact good_reflect hg

private theorem reflect_roundedIntervals {bound : Bound} {below : GridSet} {a b : Nat}
    (ha : 0 < a) (hab : a ≤ b) (hI : ∀ I ∈ below, Good I) (hbelow : ∀ I ∈ below, I.2 ≤ a) :
    IsSymmetric (denote (roundedIntervals bound below a b)) := by
  have hgood := roundedIntervals_good (bound := bound) ha hab hI hbelow
  have hmem : ∀ J ∈ roundedIntervals bound below a b,
      reflectInterval J ∈ roundedIntervals bound below a b := by
    intro J hj
    obtain ⟨I, hi, hk, hr⟩ := mem_roundedIntervals.mp hj
    refine mem_roundedIntervals.mpr ⟨I, hi, hk, ?_⟩
    rcases hr with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (reflectInterval_reflectInterval
        (scaledInterval_good bound ha hab (hbelow I hi) hk))
  ext x
  constructor
  · intro hx
    obtain ⟨J, hj, hx⟩ := mem_denote.mp hx
    have hxi : 1 - x ∈ reflect (interval J) := ⟨x, hx, rfl⟩
    rw [← interval_reflect (hgood J hj)] at hxi
    exact ⟨1 - x, mem_denote.mpr ⟨reflectInterval J, hmem J hj, hxi⟩, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨J, hj, hy⟩ := mem_denote.mp hy
    refine mem_denote.mpr ⟨reflectInterval J, hmem J hj, ?_⟩
    rw [interval_reflect (hgood J hj)]
    exact ⟨y, hy, rfl⟩

theorem scaledTarget_valid {bound : Bound} {below : GridSet} {a b : Nat}
    (ha : 0 < a) (hab : a ≤ b) (hI : ∀ I ∈ below, Good I) (hbelow : ∀ I ∈ below, I.2 ≤ a) :
    Valid (scaledTarget bound below a b) := by
  have ⟨hseg, hgrid, hdenote⟩ := mergeIntervals_spec
    (roundedIntervals_good (bound := bound) ha hab hI hbelow)
  refine ⟨hgrid, hseg, ?_⟩
  unfold scaledTarget
  rw [hdenote]
  exact reflect_roundedIntervals ha hab hI hbelow

private theorem lower_interval_subset_rescale {a b : Nat} {I : GridInterval} {r : ℝ}
    (ha : 0 < a) (hr : r ∈ Ioo (grid a) (grid b)) :
    interval (scaledInterval .lower a b I) ⊆ (fun t : ℝ => t / r) '' interval I := by
  have ha' : 0 < grid a := by rw [← grid_zero, grid_lt_iff]; exact ha
  have hr' : 0 < r := ha'.trans hr.1
  rintro x ⟨hxlo, hxhi⟩
  change grid (quotient .upper (I.1 * unit) a) ≤ x at hxlo
  change x ≤ grid (quotient .lower (I.2 * unit) b) at hxhi
  have hlo := (div_le_div_of_nonneg_left (grid_nonneg I.1) ha' hr.1.le).trans
    ((grid_quota_upper I.1 ha).trans hxlo)
  have hhi := hxhi.trans ((grid_quota_lower I.2 (d := b)).trans
    (div_le_div_of_nonneg_left (grid_nonneg I.2) hr' hr.2.le))
  exact ⟨x * r, ⟨(div_le_iff₀ hr').mp hlo, (le_div_iff₀ hr').mp hhi⟩,
    mul_div_cancel_right₀ x hr'.ne'⟩

private theorem rescale_subset_upper_interval {a b : Nat} {I : GridInterval} {r : ℝ}
    (ha : 0 < a) (hr : r ∈ Ioo (grid a) (grid b)) :
    (fun t : ℝ => t / r) '' interval I ⊆ interval (scaledInterval .upper a b I) := by
  have ha' : 0 < grid a := by rw [← grid_zero, grid_lt_iff]; exact ha
  have hr' : 0 < r := ha'.trans hr.1
  rintro x ⟨y, hy, rfl⟩
  change grid (quotient .lower (I.1 * unit) b) ≤ y / r ∧
    y / r ≤ grid (quotient .upper (I.2 * unit) a)
  constructor
  · apply (grid_quota_lower I.1 (d := b)).trans
    exact (div_le_div_of_nonneg_left (grid_nonneg I.1) hr' hr.2.le).trans
      (div_le_div_of_nonneg_right hy.1 hr'.le)
  · apply le_trans _ (grid_quota_upper I.2 ha)
    exact (div_le_div_of_nonneg_right hy.2 hr'.le).trans
      (div_le_div_of_nonneg_left (grid_nonneg I.2) ha' hr.1.le)

theorem scaledTarget_lower_subset {below : GridSet} {a b : Nat} {r : ℝ} {T : Set ℝ}
    (ha : 0 < a) (hr : r ∈ Ioo (grid a) (grid b)) (hI : ∀ I ∈ below, Good I)
    (hbelow : ∀ I ∈ below, I.2 ≤ a)
    (hprefix : T ∩ Icc 0 r = denote below) :
    denote (scaledTarget .lower below a b) ⊆ residualTarget r T := by
  have hab := (grid_lt_iff.mp (hr.1.trans hr.2)).le
  have hg := roundedIntervals_good (bound := .lower) ha hab hI hbelow
  rw [scaledTarget, (mergeIntervals_spec hg).2.2]
  intro x hx
  obtain ⟨J, hj, hx⟩ := mem_denote.mp hx
  obtain ⟨I, hi, hk, hJ⟩ := mem_roundedIntervals.mp hj
  have hsub := lower_interval_subset_rescale (I := I) ha hr
  have hto : interval (scaledInterval .lower a b I) ⊆ rescale r T := by
    unfold rescale
    rw [hprefix]
    exact hsub.trans (Set.image_mono fun _ hy => mem_denote.mpr ⟨I, hi, hy⟩)
  rcases hJ with rfl | rfl
  · exact Or.inl (hto hx)
  · have hg' := scaledInterval_good .lower ha hab (hbelow I hi) hk
    rw [interval_reflect hg'] at hx
    exact Or.inr (Set.image_mono hto hx)

theorem residualTarget_subset_scaledUpper {below : GridSet} {a b : Nat} {r : ℝ} {T : Set ℝ}
    (ha : 0 < a) (hr : r ∈ Ioo (grid a) (grid b)) (hI : ∀ I ∈ below, Good I)
    (hbelow : ∀ I ∈ below, I.2 ≤ a)
    (hprefix : T ∩ Icc 0 r = denote below) :
    residualTarget r T ⊆ denote (scaledTarget .upper below a b) := by
  have hab := (grid_lt_iff.mp (hr.1.trans hr.2)).le
  have hg := roundedIntervals_good (bound := .upper) ha hab hI hbelow
  rw [scaledTarget, (mergeIntervals_spec hg).2.2]
  have hto : rescale r T ⊆ denote (roundedIntervals .upper below a b) := by
    unfold rescale
    rw [hprefix]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨I, hi, hy⟩ := mem_denote.mp hy
    have hk := scaledUpper_kept ha hab (hI I hi)
    exact mem_denote.mpr ⟨scaledInterval .upper a b I,
      mem_roundedIntervals.mpr ⟨I, hi, hk, Or.inl rfl⟩,
      rescale_subset_upper_interval ha hr ⟨y, hy, rfl⟩⟩
  intro x hx
  rcases hx with hx | hx
  · exact hto hx
  · have hsym := reflect_roundedIntervals (bound := .upper) ha hab hI hbelow
    exact hsym.symm ▸ Set.image_mono hto hx

end

end LeastPrime.Checker
