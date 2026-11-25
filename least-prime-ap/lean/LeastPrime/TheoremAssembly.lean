import LeastPrime.DivisorTransfer
import LeastPrime.StickFrontier

/-! The density and least-prime conclusions from the probability bounds. -/

namespace LeastPrime

open Filter MeasureTheory Real Set
open scoped Topology

private theorem hasLogDivisorIn_Icc_iff {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    HasLogDivisorIn n (Icc a b) ↔ HasDivisorIn n a b := by
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans hn₁
  have hlog := log_pos hn₁
  have hdivisors (d : ℕ) (hd : d ∈ n.divisors) :
      log (d : ℝ) / log (n : ℝ) ∈ Icc a b ↔
        (n : ℝ) ^ a ≤ (d : ℝ) ∧ (d : ℝ) ≤ (n : ℝ) ^ b := by
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_ne_zero (fun h => by
      subst d
      have hzero := Nat.zero_dvd.mp hdvd
      omega)
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
    rw [mem_Icc, le_div_iff₀ hlog, div_le_iff₀ hlog,
      ← log_rpow hnpos a, ← log_rpow hnpos b,
      log_le_log_iff (rpow_pos_of_pos hnpos _) hdR,
      log_le_log_iff hdR (rpow_pos_of_pos hnpos _)]
  exact ⟨fun ⟨d, hd, h⟩ => ⟨d, hd, (hdivisors d hd).mp h⟩,
    fun ⟨d, hd, h⟩ => ⟨d, hd, (hdivisors d hd).mpr h⟩⟩

private theorem hasLogDivisorIn_symmetricIcc_iff {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    HasLogDivisorIn n (Icc a b ∪ Icc (1 - b) (1 - a)) ↔ HasLogDivisorIn n (Icc a b) := by
  constructor
  · rintro ⟨d, hd, h | h⟩
    · exact ⟨d, hd, h⟩
    · obtain ⟨_, he, heLog⟩ := complementary_divisor_logs hd
      have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
      have hlog := log_pos hn₁
      refine ⟨n / d, he, ?_⟩
      have heShare : log ((n / d : ℕ) : ℝ) / log n = 1 - log d / log n := by
        rw [heLog, sub_div, div_self hlog.ne']
      rw [heShare]
      exact ⟨by linarith only [h.2], by linarith only [h.1]⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, Or.inl h⟩

private theorem hasLogDivisorIn_Tin_iff {n : ℕ} (hn : 2 ≤ n) :
    HasLogDivisorIn n Tin ↔ HasDivisorIn n 0.142858 0.199999 := by
  unfold Tin
  have h := hasLogDivisorIn_symmetricIcc_iff hn 0.142858 0.199999
  norm_num at h ⊢
  exact h.trans (hasLogDivisorIn_Icc_iff hn _ _)

private def rationalWindow : Set ℝ := Icc (1 / 7) (1 / 5) ∪ Icc (4 / 5) (6 / 7)

private theorem hasLogDivisorIn_rationalWindow_iff {n : ℕ} (hn : 2 ≤ n) :
    HasLogDivisorIn n rationalWindow ↔ HasDivisorIn n (1 / 7) (1 / 5) := by
  unfold rationalWindow
  have h := hasLogDivisorIn_symmetricIcc_iff hn (1 / 7) (1 / 5)
  norm_num at h ⊢
  exact h.trans (hasLogDivisorIn_Icc_iff hn _ _)

private theorem rationalWindow_subset_Tout : rationalWindow ⊆ Tout := by
  rintro x (h | h)
  · exact Or.inl ⟨by linarith only [h.1], by linarith only [h.2]⟩
  · exact Or.inr ⟨by linarith only [h.1], by linarith only [h.2]⟩

/-- The rounded inner window is a finite union with all endpoints in the interior. -/
theorem Tin_interior : HasInteriorEndpoints Tin := by
  refine ⟨[(0.142858, 0.199999), (0.800001, 0.857142)], ?_, ?_⟩
  · norm_num
  · ext x
    simp [Tin, mem_intervalUnion]

/-- The rounded outer window is a finite union with all endpoints in the interior. -/
theorem Tout_interior : HasInteriorEndpoints Tout := by
  refine ⟨[(0.142857, 0.2), (0.8, 0.857143)], ?_, ?_⟩
  · norm_num
  · ext x
    simp [Tout, mem_intervalUnion]

theorem HasInteriorEndpoints.isClosedTarget {T : Set ℝ} (h : HasInteriorEndpoints T) :
    IsClosedTarget T := by
  obtain ⟨xs, hs, eq⟩ := h
  exact ⟨xs, fun i hi => ⟨(hs i hi).1.le, (hs i hi).2.1, (hs i hi).2.2.le⟩, eq⟩

/-- Proposition 8's eventual lower count inequality. -/
theorem eventually_density_lower (h : CitedFacts) {j : ℕ} (hj : 0 < j) {T : Set ℝ}
    (hT : HasInteriorEndpoints T) {a : ℝ} (ha : a < p j T) :
    ∀ᶠ Q in atTop, a * (window Q).card < windowCount Q (fun n => HasLogDivisorIn n T) :=
  eventually_density_lower_of_nullFrontier h.donnellyGrimmett hj
    (isClosed_E j hT.isClosedTarget).measurableSet (stickLaw_frontier_E_null hj hT) ha

/-- Proposition 8's eventual upper count inequality. -/
theorem eventually_density_upper (h : CitedFacts) {j : ℕ} (hj : 0 < j) {T : Set ℝ}
    (hT : HasInteriorEndpoints T) {b : ℝ} (hb : q j T < b) :
    ∀ᶠ Q in atTop, (windowCount Q (fun n => HasLogDivisorIn n T) : ℝ) < b * (window Q).card :=
  eventually_density_upper_of_nullFrontier h.donnellyGrimmett hj
    (isClosed_F j hT.isClosedTarget).measurableSet (stickLaw_frontier_F_null hj hT) hb

private theorem windowCount_le_of_imp {Q : ℝ} {P P' : ℕ → Prop}
    (h : ∀ n ∈ window Q, P n → P' n) : windowCount Q P ≤ windowCount Q P' := by
  classical
  unfold windowCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, h n hn.1 hn.2⟩

private theorem windowCount_congr {Q : ℝ} {P P' : ℕ → Prop}
    (h : ∀ n ∈ window Q, P n ↔ P' n) : windowCount Q P = windowCount Q P' :=
  le_antisymm (windowCount_le_of_imp fun n hn => (h n hn).1)
    (windowCount_le_of_imp fun n hn => (h n hn).2)

private theorem inward_count_of_numerics (hDG : DonnellyGrimmettInput) (hnum : P6Tin)
    (hfront : stickLaw 6 (frontier (E 6 Tin)) = 0) {a : ℝ} (ha : a < 0.587142) :
    ∀ᶠ Q in atTop, a * (window Q).card <
      windowCount Q (fun n => HasDivisorIn n 0.142858 0.199999) := by
  have hE : MeasurableSet (E 6 Tin) := (isClosed_E 6 Tin_interior.isClosedTarget).measurableSet
  have hlt : a < p 6 Tin := ha.trans_le hnum
  filter_upwards [eventually_density_lower_of_nullFrontier hDG (by norm_num) hE hfront hlt,
    eventually_gt_atTop (2 : ℝ)] with Q hQ hQ₂
  rw [windowCount_congr (fun n hn => hasLogDivisorIn_Tin_iff (window_mem_two_le hQ₂ hn))] at hQ
  exact hQ

theorem density_lower_of_numerics_of_nullFrontier (hDG : DonnellyGrimmettInput) (hnum : P6Tin)
    (hfront : stickLaw 6 (frontier (E 6 Tin)) = 0) : density_lower := by
  exact inward_count_of_numerics hDG hnum hfront (by norm_num)

theorem density_upper_of_numerics_of_nullFrontier (hDG : DonnellyGrimmettInput) (hnum : Q5Tout)
    (hfront : stickLaw 5 (frontier (F 5 Tout)) = 0) : density_upper := by
  have hF : MeasurableSet (F 5 Tout) := (isClosed_F 5 Tout_interior.isClosedTarget).measurableSet
  have hlt : q 5 Tout < 0.5956 := lt_of_le_of_lt hnum (by norm_num)
  unfold density_upper
  filter_upwards [eventually_density_upper_of_nullFrontier hDG (by norm_num) hF hfront hlt,
    eventually_gt_atTop (2 : ℝ)] with Q hQ hQ₂
  have hmono : windowCount Q (fun n => HasDivisorIn n (1 / 7) (1 / 5)) ≤
      windowCount Q (fun n => HasLogDivisorIn n Tout) := by
    apply windowCount_le_of_imp
    intro n hn hd
    obtain ⟨d, hdiv, hmem⟩ := (hasLogDivisorIn_rationalWindow_iff (window_mem_two_le hQ₂ hn)).mpr hd
    exact ⟨d, hdiv, rationalWindow_subset_Tout hmem⟩
  exact lt_of_le_of_lt (Nat.cast_le.mpr hmono) hQ

private theorem exceptions_eventually_small {c : ℝ} (hc : 0 < c) :
    ∀ᶠ Q : ℝ in atTop, Q / log Q < c * (window Q).card := by
  have herr : Tendsto (fun Q : ℝ => (log Q)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h := (window_card_ratio.const_mul c).sub herr
  have hpos : 0 < c * (1 / 2) - 0 := by
    rw [sub_zero]
    exact mul_pos hc (by norm_num)
  filter_upwards [h.eventually_const_lt hpos, eventually_gt_atTop (2 : ℝ)] with Q hQ hQ₂
  have hQpos : 0 < Q := by linarith
  have hlog := log_pos (show 1 < Q by linarith)
  apply (div_lt_div_iff_of_pos_right hQpos).mp
  have heq : (Q / log Q) / Q = (log Q)⁻¹ := by
    field_simp
  rw [heq, mul_div_assoc]
  change 0 < c * ((window Q).card / Q) - (log Q)⁻¹ at hQ
  linarith

private theorem windowCount_le_add_exceptions (Q : ℝ) (P good : ℕ → Prop) :
    windowCount Q P ≤ windowCount Q good + windowCount Q (fun n => P n ∧ ¬ good n) := by
  classical
  unfold windowCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter] at hn
  simp only [Finset.mem_union, Finset.mem_filter]
  by_cases hg : good n
  · exact Or.inl ⟨hn.1, hg⟩
  · exact Or.inr ⟨hn.1, hn.2, hg⟩

/-- The least-prime bound with the explicit constant `4`. -/
theorem main_four_of_numerics_of_nullFrontier (h : CitedFacts) (hnum : P6Tin)
    (hfront : stickLaw 6 (frontier (E 6 Tin)) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ mainBound 4 δ := by
  obtain ⟨δ, hδ, hbad⟩ := divisor_reduction h
  refine ⟨δ, hδ, ?_⟩
  unfold mainBound
  have hD := inward_count_of_numerics h.donnellyGrimmett hnum hfront
    (a := 0.58714) (by norm_num)
  filter_upwards [hD, hbad, exceptions_eventually_small (c := 0.00014) (by norm_num)] with
    Q hD hbad hsmall
  have hsplit := windowCount_le_add_exceptions Q (fun n => HasDivisorIn n 0.142858 0.199999)
    (fun n => AllClassesBelow n (4 * (n : ℝ) ^ (2 - δ)))
  have hsplitR : (windowCount Q (fun n => HasDivisorIn n 0.142858 0.199999) : ℝ) ≤
      (windowCount Q (fun n => AllClassesBelow n (4 * (n : ℝ) ^ (2 - δ))) : ℝ) +
      (windowCount Q (fun n => HasDivisorIn n 0.142858 0.199999 ∧
        ¬ AllClassesBelow n (4 * (n : ℝ) ^ (2 - δ))) : ℝ) := by exact_mod_cast hsplit
  change (0.587 : ℝ) * (window Q).card <
    (windowCount Q (fun n => AllClassesBelow n (4 * (n : ℝ) ^ (2 - δ))) : ℝ)
  linarith only [hD, hbad, hsmall, hsplitR]

theorem density_lower_of_numerics (hDG : DonnellyGrimmettInput) (hnum : P6Tin) : density_lower :=
  density_lower_of_numerics_of_nullFrontier hDG hnum
    (stickLaw_frontier_E_null (by norm_num) Tin_interior)

theorem density_upper_of_numerics (hDG : DonnellyGrimmettInput) (hnum : Q5Tout) : density_upper :=
  density_upper_of_numerics_of_nullFrontier hDG hnum
    (stickLaw_frontier_F_null (by norm_num) Tout_interior)

theorem main_four_of_numerics (h : CitedFacts) (hnum : P6Tin) :
    ∃ δ : ℝ, 0 < δ ∧ mainBound 4 δ :=
  main_four_of_numerics_of_nullFrontier h hnum
    (stickLaw_frontier_E_null (by norm_num) Tin_interior)

theorem main_of_numerics (h : CitedFacts) (hnum : P6Tin) : main := by
  obtain ⟨δ, hδ, hbound⟩ := main_four_of_numerics h hnum
  exact ⟨4, δ, by norm_num, hδ, hbound⟩

end LeastPrime
