import Chowla.Model.Cumulants

namespace Chowla

theorem innerRow_comm (k l : Row) : innerRow k l = innerRow l k := by
  rw [innerRow, innerRow, convolve_comm k.profile l.profile]
  congr 1
  ring

theorem inner_append_left (A B C : Amplitude) :
    inner (A ++ B) C = inner A C + inner B C := by
  simp only [inner, List.map_append, List.sum_append]

theorem inner_append_right (A B C : Amplitude) :
    inner A (B ++ C) = inner A B + inner A C := by
  simp only [inner, List.map_append, List.sum_append, List.sum_map_add]

theorem inner_comm (A B : Amplitude) : inner A B = inner B A := by
  induction A with
  | nil =>
    simp only [inner, List.map_nil, List.sum_nil]
    induction B with
    | nil => rfl
    | cons b B ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih, zero_add]
  | cons a A ih =>
    change inner ([a] ++ A) B = inner B ([a] ++ A)
    rw [inner_append_left, inner_append_right, ih]
    congr 1
    simp only [inner, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact congrArg (fun f => (B.map f).sum) (funext (innerRow_comm a))

/-- Lemma 23. A squared-gain certificate for the old rows suffices to bound the enlarged Gram
value. The argument applies to either sign of the old Gram value. -/
theorem chain (F F' : Amplitude) (U g : ℝ) (hg : 0 < g)
    (hC : 0 < inner_G F) (hU : inner_G F ≤ U)
    (hgain : 2 * g * inner F F ≤ (inner_G F) ^ 2) :
    inner (F ++ F') (F ++ F') ≤ U ^ 2 / (2 * g) + 2 * inner F F' + inner F' F' := by
  have hbound : inner F F ≤ U ^ 2 / (2 * g) := by
    apply (le_div_iff₀ (show 0 < 2 * g by positivity)).2
    rw [mul_comm]
    exact hgain.trans ((sq_le_sq₀ hC.le (hC.le.trans hU)).mpr hU)
  rw [inner_append_left, inner_append_right, inner_append_right, inner_comm F' F]
  linarith

end Chowla
