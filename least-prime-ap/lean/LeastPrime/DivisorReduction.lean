import LeastPrime.Cited
import LeastPrime.ProofDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The reduction from suitable divisors to Maynard's uniform prime bound. -/

namespace LeastPrime

open Filter Real

theorem window_mem_bounds {Q : ℝ} (hQ : 0 ≤ Q) {n : ℕ} (hn : n ∈ window Q) :
    Q / 2 < (n : ℝ) ∧ (n : ℝ) ≤ Q := by
  rw [window_eq_Ioc hQ, Finset.mem_Ioc] at hn
  have hQhalf : 0 ≤ Q / 2 := by positivity
  exact ⟨(Nat.floor_lt hQhalf).mp hn.1, (Nat.le_floor_iff hQ).mp hn.2⟩

theorem window_mem_two_le {Q : ℝ} (hQ : 2 < Q) {n : ℕ} (hn : n ∈ window Q) : 2 ≤ n := by
  have .intro hleft _ := window_mem_bounds (by positivity : 0 ≤ Q) hn
  have h : (1 : ℝ) < n := by linarith
  exact_mod_cast h

theorem complementary_divisor_logs {n d : ℕ} (hd : d ∈ n.divisors) :
    0 < ((n / d : ℕ) : ℝ) ∧
    ((n / d : ℕ) ∈ n.divisors) ∧
    log ((n / d : ℕ) : ℝ) = log n - log d := by
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := by intro h; simp [h, hn0] at hdvd
  have he0 : n / d ≠ 0 := by
    have h := Nat.mul_div_cancel' hdvd
    intro hz
    simp [hz] at h
    exact hn0 h.symm
  have hprod : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  have hLogs : log d + log ((n / d : ℕ) : ℝ) = log n := by
    rw [← log_mul (by exact_mod_cast hd0) (by exact_mod_cast he0), hprod]
  exact ⟨by exact_mod_cast Nat.pos_of_ne_zero he0,
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn0⟩, eq_sub_of_add_eq' hLogs⟩

/-- Maynard's result excludes at most `Q / log Q` of the suitable moduli from the dyadic window. -/
theorem divisor_reduction (h : CitedFacts) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ Q in atTop,
      (windowCount Q (fun n => HasDivisorIn n 0.142858 0.199999 ∧
        ¬ AllClassesBelow n (4 * (n : ℝ) ^ (2 - δ))) : ℝ) ≤ Q / log Q := by
  classical
  obtain ⟨η₀, hη₀, hmay⟩ := h.maynard
  let η : ℝ := min η₀ (1 / 100000000)
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hηsmall : η ≤ 1 / 100000000 := min_le_right _ _
  obtain ⟨x₀, hx₀, hmay⟩ := hmay η hη (min_le_left _ _)
  let s : ℝ := 2 / (1 + 2 * η)
  let δ : ℝ := 4 * η / (1 + 2 * η)
  have hden : 0 < 1 + 2 * η := by positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hs₁ : 1 ≤ s := by
    apply (le_div_iff₀ hden).2
    linarith only [hηsmall]
  have hs₂ : s ≤ 2 := by
    apply (div_le_iff₀ hden).2
    linarith only [hη]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsd : s = 2 - δ := by
    dsimp [s, δ]
    field_simp
    ring
  have hsprod : s * (1 / 2 + η) = 1 := by
    dsimp [s]
    field_simp
  have hleftCoef : (2 / 5 + 5 * η) * s ≤ 0.8000001 := by
    dsimp only [s]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    linarith only [hηsmall, hη]
  have hrightCoef : (0.857142 : ℝ) ≤ (3 / 7) * s := by
    dsimp only [s]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).2
    linarith only [hηsmall]
  have hlogTwo : 0 < log 2 := log_pos (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ),
    (tendsto_atTop.1 (tendsto_rpow_atTop hs) (x₀ + 1)),
    (tendsto_atTop.1 Real.tendsto_log_atTop (1000000 * log 2))] with Q hQ hX hlogQ
  let x : ℝ := Q ^ s
  have hQpos : 0 < Q := by positivity
  have hlogQpos : 0 < log Q := log_pos (by linarith)
  have hxpos : 0 < x := rpow_pos_of_pos hQpos _
  have hxEq : x ^ (1 / 2 + η) = Q := by
    dsimp only [x]
    rw [← rpow_mul hQpos.le, hsprod, rpow_one]
  have hxLog : log x = s * log Q := log_rpow hQpos _
  have hlogLe : log Q ≤ log x := by
    rw [hxLog]
    nlinarith only [hs₁, hlogQpos]
  have hx₀' : x₀ < x := by change x₀ + 1 ≤ x at hX; linarith only [hX]
  obtain ⟨bad, _, hbad, hgood⟩ := hmay x hx₀'
  have hcard : (bad.card : ℝ) ≤ Q / log Q := by
    rw [hxEq] at hbad
    apply hbad.trans
    exact div_le_div_of_nonneg_left hQpos.le hlogQpos hlogLe
  apply le_trans _ hcard
  unfold windowCount
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hmem
  simp only [Finset.mem_filter] at hmem
  obtain ⟨hnW, ⟨d, hd, hdl, hdu⟩, hnBad⟩ := hmem
  by_contra hnNot
  apply hnBad
  obtain ⟨hnlow, hnhigh⟩ := window_mem_bounds hQpos.le hnW
  have hn₂ : 2 ≤ n := window_mem_two_le hQ hnW
  have hnpos : 0 < (n : ℝ) := by positivity
  have hdpos : 0 < (d : ℝ) := by
    exact (rpow_pos_of_pos hnpos _).trans_le hdl
  obtain ⟨hepos, heDiv, heLog⟩ := complementary_divisor_logs hd
  let e : ℕ := n / d
  change 0 < (e : ℝ) at hepos
  change e ∈ n.divisors at heDiv
  change log e = log n - log d at heLog
  have hdLogLower : 0.142858 * log n ≤ log d := by
    rw [← log_rpow hnpos 0.142858]
    exact (log_le_log_iff (rpow_pos_of_pos hnpos _) hdpos).2 hdl
  have hdLogUpper : log d ≤ 0.199999 * log n := by
    rw [← log_rpow hnpos 0.199999]
    exact (log_le_log_iff hdpos (rpow_pos_of_pos hnpos _)).2 hdu
  have hnLogLower : log Q - log 2 ≤ log n := by
    rw [← log_div hQpos.ne' (by norm_num)]
    exact (log_lt_log (by positivity) hnlow).le
  have hnLogUpper : log n ≤ log Q := (log_le_log_iff hnpos hQpos).2 hnhigh
  have heLower : x ^ (2 / 5 + 5 * η) ≤ (e : ℝ) := by
    apply (log_le_log_iff (rpow_pos_of_pos hxpos _) hepos).1
    rw [log_rpow hxpos, hxLog, ← mul_assoc]
    have hcoef := mul_le_mul_of_nonneg_right hleftCoef hlogQpos.le
    linarith only [hcoef, heLog, hdLogUpper, hnLogLower, hlogQ, hlogTwo]
  have heUpper : (e : ℝ) ≤ x ^ (3 / 7 : ℝ) := by
    apply (log_le_log_iff hepos (rpow_pos_of_pos hxpos _)).1
    rw [log_rpow hxpos, hxLog, ← mul_assoc]
    have hcoef := mul_le_mul_of_nonneg_right hrightCoef hlogQpos.le
    linarith only [hcoef, heLog, hdLogLower, hnLogUpper]
  have hprime := hgood n (by omega) (hxEq ▸ hnhigh) hnNot ⟨e, heDiv, heLower, heUpper⟩
  have hxbound : x ≤ 4 * (n : ℝ) ^ (2 - δ) := by
    have hbase : Q < 2 * n := by linarith
    have hpow := rpow_lt_rpow hQpos.le hbase hs
    have h₂ : (2 : ℝ) ^ s ≤ 4 := by
      have hp := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs₂
      simpa [show (2 : ℝ) ^ (2 : ℝ) = 4 from by norm_num [Real.rpow_natCast]] using hp
    have hnpow : 0 ≤ (n : ℝ) ^ s := (rpow_pos_of_pos hnpos _).le
    rw [← hsd]
    calc
      x ≤ (2 * n : ℝ) ^ s := hpow.le
      _ = (2 : ℝ) ^ s * (n : ℝ) ^ s := mul_rpow (by norm_num) hnpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h₂ hnpow
  intro a ha
  obtain ⟨p, hp, hmod, hpx⟩ := hprime a ha
  exact ⟨p, hp, hmod, hpx.trans hxbound⟩

end LeastPrime
