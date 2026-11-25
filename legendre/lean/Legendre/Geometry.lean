import Legendre.AnalyticData
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Legendre

open Real

private theorem one_add_inv_eq {x : ℝ} (hx : 0 < x) : 1 + 1 / x = (x + 1) / x := by
  field_simp

private theorem rpow_sq_exponent {x r : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 : ℕ)) ^ r = x ^ (2 * r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

namespace Window

theorem ofBase_a_pos {x : ℝ} (hx : 0 < x) : 0 < (ofBase x).a :=
  Real.rpow_pos_of_pos (by positivity) _

theorem ofBase_endpoints {x : ℝ} (hx : 0 < x) :
    (ofBase x).endpoint (-1) = x ^ ((11 : ℝ) / 5) ∧
      (ofBase x).endpoint 1 = (x + 1) ^ ((11 : ℝ) / 5) := by
  have hx₁ : 0 < x + 1 := by positivity
  have he : Real.exp (ofBase x).D = ((x + 1) / x) ^ ((11 : ℝ) / 10) := by
    change Real.exp (11 / 10 * Real.log (1 + 1 / x)) = _
    rw [one_add_inv_eq hx, Real.rpow_def_of_pos (div_pos hx₁ hx), mul_comm]
  have hlo : (x * (x + 1)) / ((x + 1) / x) = x ^ (2 : ℕ) := by
    field_simp
  have hhi : (x * (x + 1)) * ((x + 1) / x) = (x + 1) ^ (2 : ℕ) := by
    field_simp
  constructor
  · simp only [endpoint, mul_neg, mul_one, Real.exp_neg, he, ← div_eq_mul_inv]
    change (x * (x + 1)) ^ ((11 : ℝ) / 10) / ((x + 1) / x) ^ ((11 : ℝ) / 10) = _
    rw [← Real.div_rpow (by positivity) (by positivity), hlo, rpow_sq_exponent hx.le]
    norm_num
  · simp only [endpoint, mul_one, he]
    change (x * (x + 1)) ^ ((11 : ℝ) / 10) * ((x + 1) / x) ^ ((11 : ℝ) / 10) = _
    rw [← Real.mul_rpow (by positivity) (by positivity), hhi, rpow_sq_exponent hx₁.le]
    norm_num

theorem ofBase_D_bounds {x : ℝ} (hx : 0 < x) :
    1.1 / (x + 1) ≤ (ofBase x).D ∧ (ofBase x).D ≤ 1.1 / x := by
  have harg : 0 < 1 + 1 / x := by positivity
  have hlo := Real.one_sub_inv_le_log_of_pos harg
  have hhi := Real.log_le_sub_one_of_pos harg
  have heq : 1 - (1 + 1 / x)⁻¹ = 1 / (x + 1) := by
    rw [one_add_inv_eq hx, inv_div]
    field_simp
    ring
  rw [heq] at hlo
  have hhi' : Real.log (1 + 1 / x) ≤ 1 / x := by linarith
  change 1.1 / (x + 1) ≤ (11 / 10) * Real.log (1 + 1 / x) ∧
    (11 / 10) * Real.log (1 + 1 / x) ≤ 1.1 / x
  rw [show (1.1 : ℝ) = 11 / 10 by norm_num]
  exact ⟨by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 11 / 10),
    by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hhi' (by norm_num : (0 : ℝ) ≤ 11 / 10)⟩

theorem ofBase_D_pos {x : ℝ} (hx : 0 < x) : 0 < (ofBase x).D :=
  lt_of_lt_of_le (by positivity) (ofBase_D_bounds hx).1

theorem ofBase_sqrt_bounds {x : ℝ} (hx : 0 < x) :
    x ^ ((11 : ℝ) / 10) ≤ Real.sqrt (ofBase x).a ∧
      Real.sqrt (ofBase x).a ≤ (x + 1) ^ ((11 : ℝ) / 10) := by
  change _ ≤ Real.sqrt ((x * (x + 1)) ^ ((11 : ℝ) / 10)) ∧ _
  have hr (t : ℝ) (ht : 0 ≤ t) : (t ^ ((11 : ℝ) / 10)) ^ (2 : ℕ) =
      (t ^ (2 : ℕ)) ^ ((11 : ℝ) / 10) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht, rpow_sq_exponent ht]
    congr 1
    norm_num
  have hmul : 0 ≤ x * (x + 1) := by positivity
  have h₁ : 0 ≤ x + 1 := by positivity
  constructor
  · rw [← Real.sqrt_sq (Real.rpow_nonneg hx.le _)]
    exact Real.sqrt_le_sqrt (by rw [hr x hx.le]; exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num))
  · rw [← Real.sqrt_sq (Real.rpow_nonneg h₁ _)]
    exact Real.sqrt_le_sqrt (by rw [hr (x + 1) h₁]; exact Real.rpow_le_rpow hmul (by nlinarith) (by norm_num))

theorem ofBase_P_bounds {x : ℝ} (hx : 0 < x) :
    1.1 * x ^ ((1 : ℝ) / 10) * (x / (x + 1)) ≤ (ofBase x).P ∧
      (ofBase x).P ≤ 1.1 / x * (x + 1) ^ ((11 : ℝ) / 10) := by
  have hpow : x ^ ((11 : ℝ) / 10) = x ^ ((1 : ℝ) / 10) * x := by
    rw [show (11 / 10 : ℝ) = 1 / 10 + 1 by norm_num, Real.rpow_add_one hx.ne']
  refine ⟨?_, mul_le_mul (ofBase_D_bounds hx).2 (ofBase_sqrt_bounds hx).2
    (Real.sqrt_nonneg _) (by positivity)⟩
  calc
    _ = 1.1 / (x + 1) * x ^ ((11 : ℝ) / 10) := by rw [hpow]; ring
    _ ≤ (ofBase x).P := mul_le_mul (ofBase_D_bounds hx).1 (ofBase_sqrt_bounds hx).1
      (by positivity) (ofBase_D_pos hx).le

theorem ofBase_L_bounds {x : ℝ} (hx : 0 < x) :
    1.1 * Real.log x ≤ (ofBase x).L ∧ (ofBase x).L ≤ 1.1 * Real.log (x + 1) := by
  have hx₁ : 0 < x + 1 := by positivity
  have hpow : 0 < x ^ ((11 : ℝ) / 10) := by positivity
  have hroot : 0 < Real.sqrt (ofBase x).a := Real.sqrt_pos.2 (ofBase_a_pos hx)
  unfold L
  constructor
  · rw [show (1.1 : ℝ) = 11 / 10 by norm_num, ← Real.log_rpow hx]
    exact Real.log_le_log hpow (ofBase_sqrt_bounds hx).1
  · rw [show (1.1 : ℝ) = 11 / 10 by norm_num, ← Real.log_rpow hx₁]
    exact Real.log_le_log hroot (ofBase_sqrt_bounds hx).2

theorem ofBase_log_inv_D_le {x : ℝ} (hx : 0 < x) :
    Real.log (1 / (ofBase x).D) ≤ Real.log ((x + 1) / 1.1) := by
  apply Real.log_le_log (by positivity [ofBase_D_pos hx])
  rw [div_le_div_iff₀ (ofBase_D_pos hx) (by norm_num : (0 : ℝ) < 1.1), one_mul]
  exact (div_le_iff₀ (by positivity : 0 < x + 1)).1 (ofBase_D_bounds hx).1 |>.trans_eq (mul_comm _ _)

theorem ofBase_W_eq {x : ℝ} (hx : 0 < x) :
    (ofBase x).W = (ofBase x).P * Real.sqrt (ofBase x).a := by
  rw [W, P, mul_assoc, Real.mul_self_sqrt (ofBase_a_pos hx).le, mul_comm]

theorem log_a_eq_two_L (w : Window) (ha : 0 ≤ w.a) : Real.log w.a = 2 * w.L := by
  rw [L, Real.log_sqrt ha]
  ring

theorem exp_L_eq_sqrt (w : Window) (ha : 0 < w.a) : Real.exp w.L = Real.sqrt w.a :=
  Real.exp_log (Real.sqrt_pos.2 ha)

theorem endpoint_pos (w : Window) (ha : 0 < w.a) (s : ℝ) : 0 < w.endpoint s :=
  mul_pos ha (Real.exp_pos _)

theorem endpoint_strictMono (w : Window) (ha : 0 < w.a) (hD : 0 < w.D) :
    StrictMono w.endpoint := fun _ _ h ↦
  mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hD)) ha

theorem scale_endpoint (w : Window) (ha : 0 < w.a) (hD : 0 < w.D) (s : ℝ) :
    w.scale (w.endpoint s) = s := by
  rw [scale, endpoint, mul_comm w.a, mul_div_cancel_right₀ _ ha.ne', Real.log_exp]
  field_simp

theorem endpoint_scale (w : Window) (ha : 0 < w.a) (hD : 0 < w.D) {t : ℝ} (ht : 0 < t) :
    w.endpoint (w.scale t) = t := by
  rw [endpoint, scale, ← mul_div_assoc, mul_div_cancel_left₀ _ hD.ne', Real.exp_log (div_pos ht ha)]
  field_simp

end Window

theorem window_exp_upper {t : ℝ} (ht : t ≤ (U - 1) / U) : Real.exp t ≤ U := by
  have hU : 0 < U := by norm_num [U]
  rw [← Real.exp_log hU]
  apply Real.exp_le_exp.mpr
  have heq : (U - 1) / U = 1 - U⁻¹ := by field_simp
  rw [heq] at ht
  exact ht.trans (Real.one_sub_inv_le_log_of_pos hU)

theorem window_exp_lower {t : ℝ} (ht : t ≤ (U - 1) / U) : 1 / U ≤ Real.exp (-t) := by
  rw [one_div, Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos _) (window_exp_upper ht)

theorem window_lower_support (w : Window) (K : ℝ) (hw : WindowBounds w K) :
    2 ≤ w.endpoint (-K) := by
  have ha := (Real.le_log_iff_exp_le hw.a_pos).mp hw.log_a
  have h61 : (61 : ℝ) ≤ Real.exp 60 := by linarith [Real.add_one_le_exp 60]
  have hphysical : w.a / U ≤ w.endpoint (-K) := by
    rw [Window.endpoint, mul_neg, mul_comm w.D K, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (window_exp_lower hw.width) hw.a_pos.le
  exact (show (2 : ℝ) ≤ 61 / U by norm_num [U]).trans <|
    (div_le_div_of_nonneg_right (h61.trans ha) (by norm_num [U])).trans hphysical

/-- Upper bound for the prime weight on the supported physical interval. -/
theorem window_weight_le (w : Window) (K : ℝ) (hw : WindowBounds w K) {t : ℝ}
    (ht₁ : w.endpoint (-K) ≤ t) (ht₂ : t ≤ w.endpoint K) :
    Real.log t / Real.sqrt t ≤ U ^ 2 * (2 * w.L) * Real.exp (-w.L) := by
  have hu : (1 : ℝ) ≤ U := by norm_num [U]
  have huv : 0 < U := zero_lt_one.trans_le hu
  have hsa : 0 < Real.sqrt w.a := Real.sqrt_pos.2 hw.a_pos
  have ht : 0 < t := (w.endpoint_pos hw.a_pos _).trans_le ht₁
  have hta : w.a / U ≤ t := by
    refine le_trans ?_ ht₁
    rw [Window.endpoint, mul_neg, mul_comm w.D K, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (window_exp_lower hw.width) hw.a_pos.le
  have hs : Real.sqrt w.a / U ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq (div_nonneg hsa.le huv.le)]
    apply Real.sqrt_le_sqrt
    rw [div_pow, Real.sq_sqrt hw.a_pos.le]
    exact (div_le_div_of_nonneg_left hw.a_pos.le huv (by norm_num [U])).trans hta
  have hlog : Real.log t ≤ Real.log w.a + K * w.D := by
    refine (Real.log_le_log ht ht₂).trans_eq ?_
    rw [Window.endpoint, Real.log_mul hw.a_pos.ne' (Real.exp_pos _).ne', Real.log_exp, mul_comm w.D K]
  have hW : K * w.D ≤ U - 1 := hw.width.trans (div_le_self (sub_nonneg.mpr hu) hu)
  have hn : Real.log t ≤ U * (2 * w.L) := by
    rw [← w.log_a_eq_two_L hw.a_pos.le]
    have hprod := mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ Real.log w.a - 1 by linarith [hw.log_a])
    nlinarith only [hlog, hW, hprod]
  have hL : 0 ≤ 2 * w.L := by rw [← w.log_a_eq_two_L hw.a_pos.le]; linarith [hw.log_a]
  calc
    _ ≤ (U * (2 * w.L)) / Real.sqrt t := div_le_div_of_nonneg_right hn (Real.sqrt_nonneg _)
    _ ≤ (U * (2 * w.L)) / (Real.sqrt w.a / U) :=
      div_le_div_of_nonneg_left (mul_nonneg huv.le hL) (div_pos hsa huv) hs
    _ = _ := by
      rw [Real.exp_neg, w.exp_L_eq_sqrt hw.a_pos]
      field_simp

theorem bridge_window_bounds {x : ℝ} (hx₁ : 35 * 10 ^ 12 ≤ x) (hx₂ : x ≤ 6 * 10 ^ 14) :
    WindowBounds (Window.ofBase x) 2 ∧ (Window.ofBase x).P < 34 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hx₁
  have ha := Window.ofBase_a_pos hx
  have hD := Window.ofBase_D_pos hx
  have hlog : 30 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx).2
    rw [show (30 : ℝ) = (↑(30 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have hE : Real.exp 1 ≤ 11 / 4 := Real.exp_one_lt_d9.le.trans (by norm_num)
    exact (pow_le_pow_left₀ (Real.exp_pos _).le hE _).trans
      ((show (11 / 4 : ℝ) ^ (30 : ℕ) ≤ 35 * 10 ^ 12 by norm_num).trans hx₁)
  have hla := (Window.ofBase_L_bounds hx).1
  have hloga : 60 ≤ Real.log (Window.ofBase x).a := by
    rw [Window.log_a_eq_two_L _ ha.le]
    nlinarith
  have hDhi := (Window.ofBase_D_bounds hx).2
  have hwidth : 2 * (Window.ofBase x).D ≤ (U - 1) / U := by
    calc
      _ ≤ 2 * (1.1 / x) := by linarith
      _ ≤ 2 * (1.1 / (35 * 10 ^ 12)) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx₁)
          (by norm_num)
      _ ≤ _ := by norm_num [U]
  have hroot : (x + 1) ^ ((1 : ℝ) / 10) < 30.5 := by
    let r : ℝ := 6 * 10 ^ 14 + 1
    have hr : 0 ≤ r := by norm_num [r]
    have hrpow : (r ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) = r := by
      rw [← Real.rpow_mul_natCast hr]
      rw [show (1 / 10 : ℝ) * ↑(10 : ℕ) = 1 by norm_num, Real.rpow_one]
    have hrlt : r ^ ((1 : ℝ) / 10) < (30.5 : ℝ) := by
      apply (pow_lt_pow_iff_left₀ (n := 10) (Real.rpow_nonneg hr _) (by norm_num) (by decide)).1
      rw [hrpow]
      norm_num [r]
    exact (Real.rpow_le_rpow (by positivity) (by dsimp [r]; linarith) (by norm_num)).trans_lt hrlt
  have hratio : (x + 1) / x ≤ 1.01 := by
    rw [← one_add_inv_eq hx]
    have hinv : 1 / x ≤ (1 : ℝ) / 100 :=
      div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
    linarith
  have hP : (Window.ofBase x).P < 34 := by
    refine (Window.ofBase_P_bounds hx).2.trans_lt ?_
    rw [show (11 / 10 : ℝ) = 1 / 10 + 1 by norm_num, Real.rpow_add_one (by positivity : x + 1 ≠ 0)]
    calc
      _ = 1.1 * ((x + 1) ^ ((1 : ℝ) / 10) * ((x + 1) / x)) := by ring
      _ ≤ 1.1 * (30.5 * 1.01) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hroot.le hratio (by positivity) (by norm_num))
          (by norm_num)
      _ < _ := by norm_num
  exact ⟨⟨ha, hD, hloga, hwidth, by linarith⟩, hP⟩

theorem scaleFactor_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x ^ ((1 : ℝ) / 10) * (x / (x + 1)) ≤ y ^ ((1 : ℝ) / 10) * (y / (y + 1)) := by
  have hy : 0 < y := hx.trans_le hxy
  have hfrac : x / (x + 1) ≤ y / (y + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  exact mul_le_mul (Real.rpow_le_rpow hx.le hxy (by norm_num)) hfrac (by positivity) (by positivity)

private theorem exp_sub_bounds (u v : ℝ) :
    (u - v) * Real.exp v ≤ Real.exp u - Real.exp v ∧
      Real.exp u - Real.exp v ≤ (u - v) * Real.exp u := by
  have hlo := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (u - v)) (Real.exp_pos v).le
  have hhi := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (v - u)) (Real.exp_pos u).le
  rw [← Real.exp_add, sub_add_cancel] at hlo hhi
  constructor <;> linarith

/-- Lemma 18, the right and left shoulder lengths. -/
theorem shoulder_lengths (w : Window) (K : ℝ) (hw : WindowBounds w K)
    (s₁ s₂ : ℝ) (hs₁ : 1 ≤ s₁) (hs₂ : s₁ ≤ s₂) (hsK : s₂ ≤ K) :
    let v := s₂ - s₁
    w.W * v ≤ w.endpoint s₂ - w.endpoint s₁ ∧
    w.endpoint s₂ - w.endpoint s₁ ≤ w.W * v * U ∧
    w.W * v / U ≤ w.endpoint (-s₁) - w.endpoint (-s₂) ∧
    w.endpoint (-s₁) - w.endpoint (-s₂) ≤ w.W * v := by
  dsimp only [Window.W, Window.endpoint]
  have h₁ : 0 ≤ w.D * s₁ := mul_nonneg hw.D_pos.le (by linarith)
  have h₂ : w.D * s₂ ≤ K * w.D := by
    rw [mul_comm K]
    exact mul_le_mul_of_nonneg_left hsK hw.D_pos.le
  have hlen : 0 ≤ w.D * (s₂ - s₁) := mul_nonneg hw.D_pos.le (sub_nonneg.mpr hs₂)
  have hpos : 1 ≤ Real.exp (w.D * s₁) := Real.one_le_exp h₁
  have hneg : Real.exp (w.D * -s₁) ≤ 1 := by
    rw [mul_neg]
    exact Real.exp_le_one_iff.2 (neg_nonpos.mpr h₁)
  have hp := window_exp_upper (h₂.trans hw.width)
  have hn : 1 / U ≤ Real.exp (w.D * -s₂) := by
    rw [mul_neg]
    exact window_exp_lower (h₂.trans hw.width)
  have hr := exp_sub_bounds (w.D * s₂) (w.D * s₁)
  have hl := exp_sub_bounds (w.D * -s₁) (w.D * -s₂)
  rw [show w.D * s₂ - w.D * s₁ = w.D * (s₂ - s₁) by ring] at hr
  rw [show w.D * -s₁ - w.D * -s₂ = w.D * (s₂ - s₁) by ring] at hl
  have ha := hw.a_pos.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [mul_sub, ← mul_assoc] using
      mul_le_mul_of_nonneg_left ((le_mul_of_one_le_right hlen hpos).trans hr.1) ha
  · simpa only [mul_sub, ← mul_assoc] using
      mul_le_mul_of_nonneg_left (hr.2.trans (mul_le_mul_of_nonneg_left hp hlen)) ha
  · rw [div_eq_mul_one_div]
    simpa only [mul_sub, ← mul_assoc] using
      mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hn hlen).trans hl.1) ha
  · simpa only [mul_sub, ← mul_assoc, mul_one] using
      mul_le_mul_of_nonneg_left (hl.2.trans (mul_le_mul_of_nonneg_left hneg hlen)) ha

end Legendre
