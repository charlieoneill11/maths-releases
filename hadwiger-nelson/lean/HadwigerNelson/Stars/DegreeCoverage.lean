import HadwigerNelson.Stars.CreditSound

/-! Degree ranges for the complete-wave certificate. The native term increases
with d, while the right side of the required Fejér inequality decreases with d. -/

namespace HadwigerNelson.Stars.BoxCheck
open scoped BigOperators

theorem checkData_spec (rows : Array Row) (sat : Array (Int × Int)) (pass : checkData rows sat = true) :
    (∀ d : Nat, 23 ≤ d → d ≤ 27 → checkDegree rows sat d = true) ∧
    targetPass 28 (nativeNumerator sat 28) 0 = true := by
  rw [checkData,Bool.and_eq_true,array_all_ofFn] at pass
  refine ⟨?_,pass.2⟩
  intro d dl dr
  have h := pass.1 ⟨d-23,by omega⟩
  exact (show 23+(d-23) = d by omega) ▸ h

/-- Numerator decoding expresses the native contribution as an area-weighted
sum of positive parts. -/
theorem nativeValue_eq (sat : Array (Int × Int)) (d : Nat) (hd : 0 < d) :
    nativeValue d (nativeNumerator sat d) = ∑ i : Fin sat.size,
      (4*(sat[i.val].1 : ℝ)/CompleteWave.xInt) *
        max 0 ((sat[i.val].2 : ℝ)/quant-1/d) := by
  unfold nativeValue nativeNumerator
  rw [array_sum_by,Int.cast_sum,div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  let a : ℝ := sat[k.val].1
  let f : ℝ := sat[k.val].2
  have hr : (0 : ℝ) < d := by exact_mod_cast hd
  push_cast
  change (4*a*max 0 (f*d-quant)) * _ = (4*a/CompleteWave.xInt) * max 0 (f/quant-1/d)
  by_cases h : 0 ≤ f*d-quant
  · rw [max_eq_right h,max_eq_right]
    · norm_num [quant,CompleteWave.xInt]
      field_simp
      ring
    · apply sub_nonneg.mpr
      apply (div_le_div_iff₀ hr (by norm_num [quant])).2
      linarith
  · rw [max_eq_left (le_of_not_ge h),max_eq_left]
    · simp
    · apply sub_nonpos.mpr
      apply (div_le_div_iff₀ (by norm_num [quant]) hr).2
      linarith

theorem nativeValue_mono (sat : Array (Int × Int)) (areas : ∀ i : Fin sat.size, 0 ≤ sat[i.val].1)
    {d e : Nat} (hd : 0 < d) (de : d ≤ e) :
    nativeValue d (nativeNumerator sat d) ≤ nativeValue e (nativeNumerator sat e) := by
  rw [nativeValue_eq sat d hd,nativeValue_eq sat e (hd.trans_le de)]
  apply Finset.sum_le_sum
  intro i _
  have ha : (0 : ℝ) ≤ sat[i.val].1 := by exact_mod_cast areas i
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have de' : (d : ℝ) ≤ e := by exact_mod_cast de
  have inv := one_div_le_one_div_of_le hd' de'
  apply mul_le_mul_of_nonneg_left (max_le_max_left 0 (sub_le_sub_left inv _))
  exact div_nonneg (mul_nonneg (by norm_num) ha) (by norm_num [CompleteWave.xInt])

/-- For degrees below 23 the d=23 spectral requirement is the weakest one. -/
theorem fejer_requirement_antitone {K d e : Nat} (hd : 0 < d) (de : d ≤ e) :
    ((K+1 : ℝ)/e-1) ≤ ((K+1 : ℝ)/d-1) :=
  sub_le_sub_right (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hd)
    (by exact_mod_cast de)) _

end HadwigerNelson.Stars.BoxCheck
