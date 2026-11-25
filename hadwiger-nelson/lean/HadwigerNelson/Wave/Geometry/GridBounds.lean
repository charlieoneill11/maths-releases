import HadwigerNelson.Angular.Grid

namespace HadwigerNelson.Angular.Grid

theorem interpolation_mono (v : Nat → ℝ) (n : Nat) (h : ∀ i<n, v i ≤ v (i+1)) :
    Monotone (interpolation v n) := by
  induction n with
  | zero => exact monotone_const
  | succ n ih =>
    have old := ih (fun i hi => h i (by omega))
    have last := h n (Nat.lt_succ_self _)
    intro a b hab
    by_cases hb : b ≤ (n:ℝ)
    · simpa [interpolation,if_pos hb,if_pos (hab.trans hb)] using old hab
    · by_cases ha : a ≤ (n:ℝ)
      · rw [interpolation,if_pos ha,interpolation,if_neg hb]
        have prev := old ha
        rw [interpolation_right] at prev
        nlinarith [mul_nonneg (sub_nonneg.mpr last) (sub_nonneg.mpr (le_of_not_ge hb))]
      · rw [interpolation,if_neg ha,interpolation,if_neg hb]
        exact add_le_add_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hab _) (sub_nonneg.mpr last)) _

theorem interpolation_neg (v : Nat → ℝ) (n : Nat) (t : ℝ) :
    interpolation (fun i => -(v i)) n t = -(interpolation v n t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [interpolation]
    split_ifs <;> first | exact ih | ring

theorem interpolation_anti (v : Nat → ℝ) (n : Nat) (h : ∀ i<n, v (i+1) ≤ v i) :
    Antitone (interpolation v n) := by
  have mono := interpolation_mono (fun i => -(v i)) n (fun i hi => neg_le_neg (h i hi))
  intro a b hab
  simpa only [interpolation_neg,neg_le_neg_iff] using mono hab

private theorem linear_shift (v : Nat → ℝ) (a : ℝ) {n : Nat} (hn : 0<n)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (n:ℝ)) :
    interpolation (fun i => v i+a*(i:ℝ)) n t = interpolation v n t+a*t := by
  obtain ⟨i,hi,it⟩ := hasCell hn ht
  rw [interpolation_on _ hi it,interpolation_on v hi it]
  push_cast
  ring

/-- A bound on every adjacent difference bounds the change of the real
piecewise-linear interpolant on the entire interval, including at knots. -/
theorem interpolation_lipschitz (v : Nat → ℝ) (n : Nat) (hn : 0<n) (A : ℝ)
    (slope : ∀ i<n, |v (i+1)-v i| ≤ A) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 (n:ℝ)) (hu : u ∈ Set.Icc 0 (n:ℝ)) :
    |interpolation v n t-interpolation v n u| ≤ A*|t-u| := by
  have inc := interpolation_mono (fun i => v i + A*(i:ℝ)) n (fun i hi => by
    have b := (abs_le.mp (slope i hi)).1
    push_cast; linarith)
  have dec := interpolation_anti (fun i => v i + (-A)*(i:ℝ)) n (fun i hi => by
    have b := (abs_le.mp (slope i hi)).2
    push_cast; linarith)
  rcases le_total t u with le | le
  · have hi := inc le; have hd := dec le
    rw [linear_shift v A hn ht,linear_shift v A hn hu] at hi
    rw [linear_shift v (-A) hn ht,linear_shift v (-A) hn hu] at hd
    rw [abs_of_nonpos (sub_nonpos.mpr le),abs_le]
    constructor <;> linarith
  · have hi := inc le; have hd := dec le
    rw [linear_shift v A hn ht,linear_shift v A hn hu] at hi
    rw [linear_shift v (-A) hn ht,linear_shift v (-A) hn hu] at hd
    rw [abs_of_nonneg (sub_nonneg.mpr le),abs_le]
    constructor <;> linarith

end HadwigerNelson.Angular.Grid
