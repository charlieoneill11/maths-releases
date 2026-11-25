import Legendre.PrimeCounting
import Legendre.ShoulderLayers

namespace Legendre

open Finset
open scoped BigOperators

private theorem window_W_eq_P_exp (w : Window) (ha : 0 < w.a) : w.W = w.P * Real.exp w.L := by
  rw [w.exp_L_eq_sqrt ha, Window.W, Window.P, mul_assoc, ← sq, Real.sq_sqrt ha.le, mul_comm]

private theorem window_W_pos (w : Window) (hw : WindowBounds w 2) : 0 < w.W :=
  mul_pos hw.a_pos hw.D_pos

private theorem window_P_pos (w : Window) (hw : WindowBounds w 2) : 0 < w.P :=
  mul_pos hw.D_pos (Real.sqrt_pos.2 hw.a_pos)

private theorem count_one_side (h : CitedFacts) (w : Window) (hw : WindowBounds w 2)
    {S : Finset ℕ} {a b v P₀ c : ℝ} (ha : 0 < a)
    (hs : ∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hv : (1 : ℝ) / 4000 ≤ v) (hP₀ : 0 < P₀) (hP : P₀ ≤ w.P) (hW : 4000 * U₁ < w.W)
    (hc : c ≤ Real.log (P₀ * v) - Real.log U₁) (hLc : 0 < w.L + c)
    (hlen₁ : w.W * v / U ≤ b - a) (hlen₂ : b - a ≤ w.W * v * U) :
    (S.card : ℝ) ≤ 2 * (w.W * v * U) / (w.L + c) + 1 := by
  have hv' : 0 < v := (by norm_num : (0 : ℝ) < 1 / 4000).trans_le hv
  have hU : 0 < U := by norm_num [U]
  have hU₁ : 0 < U₁ := by norm_num [U₁]
  have hUU₁ : U ≤ U₁ := by norm_num [U, U₁]
  have hlen : 1 < b - a := by
    apply lt_of_lt_of_le _ hlen₁
    apply (lt_div_iff₀ hU).mpr
    have hW' := mul_lt_mul_of_pos_right hW hv'
    have hv₁ : 1 ≤ 4000 * v := by linarith
    have hscale : U₁ ≤ (4000 * U₁) * v := by
      calc
        _ ≤ U₁ * (4000 * v) := le_mul_of_one_le_right hU₁.le hv₁
        _ = _ := by ring
    simpa only [one_mul] using hUU₁.trans_lt (hscale.trans_lt hW')
  have hc' : Real.exp c ≤ P₀ * v / U₁ := by
    have he := Real.exp_le_exp.mpr hc
    rw [Real.exp_sub, Real.exp_log (mul_pos hP₀ hv'), Real.exp_log hU₁] at he
    exact he
  have hte : Real.exp (w.L + c) ≤ b - a := by
    rw [Real.exp_add]
    calc
      _ ≤ Real.exp w.L * (P₀ * v / U₁) := mul_le_mul_of_nonneg_left hc' (Real.exp_pos _).le
      _ ≤ Real.exp w.L * (w.P * v / U) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hP hv'.le) hU₁.le).trans
          (div_le_div_of_nonneg_left (mul_nonneg (window_P_pos w hw).le hv'.le) hU hUU₁)
      _ = w.W * v / U := by rw [window_W_eq_P_exp w hw.a_pos]; ring
      _ ≤ _ := hlen₁
  have hlog := (Real.le_log_iff_exp_le (zero_lt_one.trans hlen)).mpr hte
  calc
    _ ≤ 2 * (b - a) / Real.log (b - a) + 1 := primeCount_bound_closed h ha hlen hs
    _ ≤ 2 * (b - a) / (w.L + c) + 1 :=
      add_le_add_left (div_le_div_of_nonneg_left (by linarith) hLc hlog) 1
    _ ≤ _ := add_le_add_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlen₂ (by norm_num)) hLc.le) 1

private theorem prefix_card_bound (h : CitedFacts) (w : Window) (hw : WindowBounds w 2)
    {j : ℕ} (hj : j ∈ Icc 1 4000) {P₀ c : ℝ} (hP₀ : 0 < P₀) (hP : P₀ ≤ w.P)
    (hW : 4000 * U₁ < w.W) (hLc : 0 < w.L + c)
    (hc : c ≤ Real.log (P₀ * ((j : ℝ) / 4000)) - Real.log U₁) :
    ((shoulderPrefix w j).card : ℝ) ≤ 2 * (2 * (w.W * ((j : ℝ) / 4000) * U) / (w.L + c) + 1) := by
  classical
  let v : ℝ := (j : ℝ) / 4000
  let pos := (shoulderPrefix w j).filter (fun p : ℕ ↦ 0 ≤ w.scale p)
  let neg := (shoulderPrefix w j).filter (fun p : ℕ ↦ ¬ 0 ≤ w.scale p)
  obtain ⟨hj₀, hj₁⟩ := mem_Icc.mp hj
  have hv : (1 : ℝ) / 4000 ≤ v := by
    dsimp [v]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast hj₀
  have hv' : 0 ≤ v := (by norm_num : (0 : ℝ) ≤ 1 / 4000).trans hv
  have hvt : 1 + v ≤ 2 := by
    have h := (show (j : ℝ) ≤ 4000 by exact_mod_cast hj₁)
    dsimp [v]
    linarith
  have hU : 1 ≤ U := by norm_num [U]
  have hU' : 0 < U := zero_lt_one.trans_le hU
  have hWv : 0 ≤ w.W * v := mul_nonneg (window_W_pos w hw).le hv'
  have hlow : w.W * v / U ≤ w.W * v := div_le_self hWv hU
  have hhigh : w.W * v ≤ w.W * v * U := le_mul_of_one_le_right hWv hU
  have hmono := (w.endpoint_strictMono hw.a_pos hw.D_pos).monotone
  obtain ⟨hr₁, hr₂, hl₁, hl₂⟩ := shoulder_lengths w 2 hw 1 (1 + v) le_rfl (by linarith) hvt
  simp only [add_sub_cancel_left] at hr₁ hr₂ hl₁ hl₂
  have hpos : (pos.card : ℝ) ≤ 2 * (w.W * v * U) / (w.L + c) + 1 := by
    refine count_one_side h w hw (w.endpoint_pos hw.a_pos 1) ?_ hv hP₀ hP hW hc hLc
      (hlow.trans hr₁) hr₂
    intro p hp
    obtain ⟨hp', hsign⟩ := mem_filter.mp hp
    obtain ⟨hp'', hs⟩ := (mem_shoulderPrefix w j p).mp hp'
    obtain ⟨_, hprime, hlo, _⟩ := (mem_shoulderPrimes w p).mp hp''
    rw [abs_of_nonneg hsign] at hs hlo
    have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    exact ⟨hprime, (hmono hlo.le).trans_eq (w.endpoint_scale hw.a_pos hw.D_pos hpR),
      (w.endpoint_scale hw.a_pos hw.D_pos hpR).symm.trans_le (hmono hs)⟩
  have hneg : (neg.card : ℝ) ≤ 2 * (w.W * v * U) / (w.L + c) + 1 := by
    refine count_one_side h w hw (w.endpoint_pos hw.a_pos (-(1 + v))) ?_ hv hP₀ hP hW hc hLc
      hl₁ (hl₂.trans hhigh)
    intro p hp
    obtain ⟨hp', hsign⟩ := mem_filter.mp hp
    obtain ⟨hp'', hs⟩ := (mem_shoulderPrefix w j p).mp hp'
    obtain ⟨_, hprime, hlo, _⟩ := (mem_shoulderPrimes w p).mp hp''
    rw [abs_of_neg (lt_of_not_ge hsign)] at hs hlo
    have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    exact ⟨hprime, (hmono (neg_le.mp hs)).trans_eq (w.endpoint_scale hw.a_pos hw.D_pos hpR),
      (w.endpoint_scale hw.a_pos hw.D_pos hpR).symm.trans_le (hmono (by linarith))⟩
  have hcard : ((shoulderPrefix w j).card : ℝ) = (pos.card : ℝ) + (neg.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := shoulderPrefix w j)
      (p := fun p : ℕ ↦ 0 ≤ w.scale p)).symm
  rw [hcard]
  linarith

private theorem choose_endpoint_ratio {L lo hi c : ℝ} (hl : lo ≤ L) (hh : L ≤ hi)
    (hc : 0 < lo + c) :
    let M := if 0 ≤ c then hi else lo
    L / (L + c) ≤ M / (M + c) := by
  have hL : 0 < L + c := by linarith
  dsimp only
  split_ifs with h
  · apply (div_le_div_iff₀ hL (by linarith)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hh h]
  · apply (div_le_div_iff₀ hL hc).mpr
    nlinarith only [mul_le_mul_of_nonpos_right hl (le_of_not_ge h)]

/-- Lemma 21, the shoulder charge with the allowances for physical endpoints. -/
theorem shoulder_sum_bound (h : CitedFacts) (x : ℝ) (hx₁ : 35 * 10 ^ 12 ≤ x)
    (hx₂ : x ≤ 6 * 10 ^ 14) (e : ℕ → ℚ) (he : ShoulderSteps e)
    (P₀ lo hi : ℝ) (hP₀ : 0 < P₀) (hlo : 0 < lo) (_hhi : 0 < hi)
    (hP : P₀ ≤ (Window.ofBase x).P) (hL₁ : lo ≤ (Window.ofBase x).L)
    (hL₂ : (Window.ofBase x).L ≤ hi) (hW : 4000 * U₁ < (Window.ofBase x).W)
    (b : ℕ → ℝ) (hb : ∀ j : ℕ, j ∈ Finset.Icc 1 4000 → e (j + 1) < e j →
      b j ≤ Real.log (P₀ * ((j : ℝ) / 4000)) - Real.log U₁ ∧ 0 < lo + b j) :
    let w := Window.ofBase x
    shoulderSum w twelveMode ≤ w.P * shoulderCharge e b lo hi +
      4 * U ^ 2 * (e 1 : ℝ) * hi * Real.exp (-w.L) := by
  classical
  dsimp only
  let w := Window.ofBase x
  let B := U ^ 2 * (2 * w.L) * Real.exp (-w.L)
  have hw : WindowBounds w 2 := (bridge_window_bounds hx₁ hx₂).1
  have hL : 0 < w.L := hlo.trans_le hL₁
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBprimes : ∀ p ∈ shoulderPrimes w, Real.log p / Real.sqrt (p : ℝ) ≤ B := by
    intro p hp
    obtain ⟨_, hprime, _, hpp⟩ := (mem_shoulderPrimes w p).mp hp
    change |w.scale p| ≤ 2 at hpp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hmono := (w.endpoint_strictMono hw.a_pos hw.D_pos).monotone
    have hEq := w.endpoint_scale hw.a_pos hw.D_pos hpR
    exact window_weight_le w 2 hw ((hmono (abs_le.mp hpp).1).trans_eq hEq)
      (hEq.symm.trans_le (hmono (abs_le.mp hpp).2))
  apply (shoulderSum_le_layers w e he B hB hBprimes).trans
  let T (j : ℕ) := if 0 ≤ b j then hi else lo
  let v (j : ℕ) : ℝ := (j : ℝ) / 4000
  have hlocal (j : ℕ) (hj : j ∈ Icc 1 4000) :
      B * (shoulderDrop e j * (shoulderPrefix w j).card) ≤
        (8 * U₁ ^ 2 * w.P) * (shoulderDrop e j * v j * T j / (T j + b j)) + 2 * B * shoulderDrop e j := by
    by_cases hd : shoulderDrop e j = 0
    · simp [hd]
    have hdpos := lt_of_le_of_ne (shoulderDrop_nonneg e he hj) (Ne.symm hd)
    have hdrop : e (j + 1) < e j := Rat.cast_lt.mp (sub_pos.mp hdpos)
    obtain ⟨hc, hcpos⟩ := hb j hj hdrop
    have hLc : 0 < w.L + b j := by linarith
    have hunif := prefix_card_bound h w hw hj hP₀ hP hW hLc hc
    have hr : w.L / (w.L + b j) ≤ T j / (T j + b j) := choose_endpoint_ratio hL₁ hL₂ hcpos
    have hv : 0 ≤ v j := by dsimp [v]; positivity
    have hWexp : w.W * Real.exp (-w.L) = w.P := by
      rw [window_W_eq_P_exp w hw.a_pos, mul_assoc, ← Real.exp_add]
      simp
    have hU : U ^ 3 ≤ U₁ ^ 2 := by norm_num [U, U₁]
    have hWP : 0 ≤ w.P := (window_P_pos w hw).le
    calc
      _ ≤ B * (shoulderDrop e j * (2 * (2 * (w.W * v j * U) / (w.L + b j) + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hunif hdpos.le) hB
      _ = 8 * U ^ 3 * w.P * v j * (w.L / (w.L + b j)) * shoulderDrop e j +
          2 * B * shoulderDrop e j := by
        conv_lhs => rw [show B = U ^ 2 * (2 * w.L) * Real.exp (-w.L) from rfl]
        rw [← hWexp]
        dsimp [B]
        ring
      _ ≤ _ := by
        have hmul : 8 * U ^ 3 * w.P * v j * (w.L / (w.L + b j)) ≤
            8 * U₁ ^ 2 * w.P * v j * (T j / (T j + b j)) := by
          have hm : 8 * U ^ 3 * w.P * v j ≤ 8 * U₁ ^ 2 * w.P * v j := by
            gcongr
          exact (mul_le_mul_of_nonneg_right hm (div_nonneg hL.le hLc.le)).trans
            (mul_le_mul_of_nonneg_left hr (by positivity))
        convert add_le_add_left (mul_le_mul_of_nonneg_right hmul hdpos.le) (2 * B * shoulderDrop e j) using 1
        ring
  have hmain := Finset.sum_le_sum (s := Icc (1 : ℕ) 4000) hlocal
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_shoulderDrop e he (by decide : 1 ≤ 4000)] at hmain
  have he₁ : 0 ≤ (e 1 : ℝ) := Rat.cast_nonneg.mpr (he.nonneg 1 le_rfl (by decide))
  calc
    _ ≤ (8 * U₁ ^ 2 * w.P) * (∑ j ∈ Icc (1 : ℕ) 4000,
        shoulderDrop e j * v j * T j / (T j + b j)) + 2 * B * (e 1 : ℝ) := hmain
    _ = w.P * shoulderCharge e b lo hi + 2 * B * (e 1 : ℝ) := by
      unfold shoulderCharge
      simp only [shoulderDrop, v, T]
      ring
    _ ≤ _ := by
      apply add_le_add_right _
      dsimp [B]
      have hh : (2 * (U ^ 2 * (2 * w.L) * Real.exp (-w.L))) * (e 1 : ℝ) ≤
          (2 * (U ^ 2 * (2 * hi) * Real.exp (-w.L))) * (e 1 : ℝ) := by
        gcongr
      convert hh using 1
      ring

end Legendre
