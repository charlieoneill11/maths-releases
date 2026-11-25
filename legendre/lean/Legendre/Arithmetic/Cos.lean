import Legendre.Arithmetic.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace Legendre.Arithmetic

open scoped BigOperators
open Finset

/-- The first `n` terms of the real cosine series. -/
noncomputable def cosineTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range n, (-1 : ℝ) ^ j * x ^ (2 * j) / (2 * j).factorial

private theorem cosineTail_antitone {x : ℝ} (hx : 0 ≤ x) (hx₂ : x ≤ 2) :
    Antitone (fun j : ℕ ↦ x ^ (2 * (j + 1)) / ((2 * (j + 1)).factorial : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro j
  let n := 2 * (j + 1)
  change x ^ (2 * (j + 1 + 1)) / ((2 * (j + 1 + 1)).factorial : ℝ) ≤
    x ^ n / (n.factorial : ℝ)
  rw [show 2 * (j + 1 + 1) = n + 1 + 1 by dsimp [n]; omega]
  have hn : 2 ≤ (n : ℝ) := by exact_mod_cast (show 2 ≤ n by dsimp [n]; omega)
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hden : 0 < ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1) := by positivity
  have hp : x ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ hx hx₂ 2
    norm_num at h
    exact h
  have hdiv : x ^ 2 / (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1)) ≤ 1 :=
    (div_le_one hden).mpr (hp.trans (by nlinarith))
  calc
    _ = (x ^ n / (n.factorial : ℝ)) * (x ^ 2 / (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1))) := by
      rw [show n + 1 + 1 = n + 2 by omega, pow_add, show n + 2 = n + 1 + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      field_simp
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hdiv

/-- The partial sums through degrees `4*k+2` and `4*k` enclose `cos x` on `[0,2]`. -/
theorem cosineTaylor_bracket (x : ℝ) (hx : 0 ≤ x) (hx₂ : x ≤ 2) (k : ℕ) :
    cosineTaylor (2 * k + 2) x ≤ Real.cos x ∧ Real.cos x ≤ cosineTaylor (2 * k + 1) x := by
  let f (j : ℕ) : ℝ := x ^ (2 * (j + 1)) / ((2 * (j + 1)).factorial : ℝ)
  let term (j : ℕ) : ℝ := (-1 : ℝ) ^ j * x ^ (2 * j) / ((2 * j).factorial : ℝ)
  have hf : Antitone f := cosineTail_antitone hx hx₂
  have hterm (j : ℕ) : term (j + 1) = -((-1 : ℝ) ^ j * f j) := by
    simp only [term, f, pow_succ (-1 : ℝ)]
    ring
  have hsum : HasSum (fun j : ℕ ↦ (-1 : ℝ) ^ j * f j) (1 - Real.cos x) := by
    have h : HasSum term (Real.cos x) := Real.hasSum_cos x
    have h := ((hasSum_nat_add_iff' 1).mpr h).neg
    simpa only [hterm, neg_neg, sum_range_one, term, mul_zero, pow_zero, one_mul,
      Nat.factorial_zero, Nat.cast_one, div_one, neg_sub] using h
  have hsplit (n : ℕ) : cosineTaylor (n + 1) x = 1 - ∑ j ∈ range n, (-1 : ℝ) ^ j * f j := by
    change ∑ j ∈ range (n + 1), term j = _
    rw [sum_range_succ']
    simp_rw [hterm, sum_neg_distrib]
    simp [term, sub_eq_add_neg, add_comm]
  have hodd := Antitone.tendsto_le_alternating_series hsum.tendsto_sum_nat hf k
  have heven := Antitone.alternating_series_le_tendsto hsum.tendsto_sum_nat hf k
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, hsplit, hsplit]
  constructor <;> linarith

private def cosineTaylorRat (n : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ range n, (-1 : ℚ) ^ j * x ^ (2 * j) / (2 * j).factorial

@[simp] private theorem cast_cosineTaylorRat (n : ℕ) (x : ℚ) :
    (cosineTaylorRat n x : ℝ) = cosineTaylor n x := by
  simp [cosineTaylorRat, cosineTaylor]

private def cosScale : ℕ := 10 ^ 18

private def cosFirstQuadrant (q : ℚ) : Bounds :=
  (⟨cosineTaylorRat 12 (piBounds.hi * q), cosineTaylorRat 13 (piBounds.lo * q)⟩ : Bounds).round cosScale

private theorem cosFirstQuadrant_sound {q : ℚ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) :
    (cosFirstQuadrant q).Encloses (Real.cos (Real.pi * q)) := by
  apply Bounds.round_sound _ _ (by unfold cosScale; positivity)
  have hq₀' : 0 ≤ (q : ℝ) := by exact_mod_cast hq₀
  have hq₁' : (q : ℝ) ≤ 1 / 2 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hq₁
  have hlo : 0 ≤ (piBounds.lo : ℝ) := by norm_num [piBounds]
  have hhi : 0 ≤ (piBounds.hi : ℝ) := by norm_num [piBounds]
  have hloq := mul_le_mul_of_nonneg_right piBounds_sound.1 hq₀'
  have hhiq := mul_le_mul_of_nonneg_right piBounds_sound.2 hq₀'
  have hsmall : (piBounds.hi : ℝ) * (q : ℝ) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hq₁' hhi).trans (by norm_num [piBounds])
  have hpi : (piBounds.hi : ℝ) * (q : ℝ) ≤ Real.pi :=
    (mul_le_mul_of_nonneg_left hq₁' hhi).trans ((show (piBounds.hi : ℝ) * (1 / 2) ≤
      (piBounds.lo : ℝ) by norm_num [piBounds]).trans piBounds_sound.1)
  have hπlo := Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hlo hq₀') (hhiq.trans hpi) hloq
  have hπhi := Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le hq₀') hpi hhiq
  have hlow := (cosineTaylor_bracket ((piBounds.hi : ℝ) * q) (mul_nonneg hhi hq₀') hsmall 5).1
  have hupp := (cosineTaylor_bracket ((piBounds.lo : ℝ) * q) (mul_nonneg hlo hq₀')
    (hloq.trans (hhiq.trans hsmall)) 6).2
  simpa [Bounds.Encloses] using And.intro (hlow.trans hπhi) (hπlo.trans hupp)

private def phase (q : ℚ) : ℚ := q - 2 * ((⌊q / 2⌋ : ℤ) : ℚ)

private theorem phase_bounds (q : ℚ) : 0 ≤ phase q ∧ phase q < 2 := by
  have hlo := Int.floor_le (q / 2)
  have hhi := Int.lt_floor_add_one (q / 2)
  unfold phase
  constructor <;> linarith

private theorem cos_phase (q : ℚ) : Real.cos (Real.pi * phase q) = Real.cos (Real.pi * q) := by
  rw [show Real.pi * (phase q : ℝ) = Real.pi * (q : ℝ) -
    (⌊q / 2⌋ : ℤ) * (2 * Real.pi) by push_cast [phase]; ring]
  exact Real.cos_sub_int_mul_two_pi _ _

private def foldPhase (q : ℚ) : ℚ := if phase q ≤ 1 then phase q else 2 - phase q

private theorem foldPhase_spec (q : ℚ) :
    (0 ≤ foldPhase q ∧ foldPhase q ≤ 1) ∧
      Real.cos (Real.pi * foldPhase q) = Real.cos (Real.pi * q) := by
  obtain ⟨hlo, hhi⟩ := phase_bounds q
  unfold foldPhase
  split
  · exact ⟨⟨hlo, by assumption⟩, cos_phase q⟩
  · rename_i ha
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rw [show Real.pi * (↑(2 - phase q) : ℝ) = 2 * Real.pi - Real.pi * (phase q : ℝ) by
      push_cast; ring, Real.cos_two_pi_sub, cos_phase]

/-- Reduce modulo two and use the first-quadrant Taylor enclosure. -/
def cosPi (q : ℚ) : Bounds :=
  let r := foldPhase q
  if r ≤ 1 / 2 then cosFirstQuadrant r else (cosFirstQuadrant (1 - r)).neg

theorem cosPi_sound (q : ℚ) : (cosPi q).Encloses (Real.cos (Real.pi * q)) := by
  obtain ⟨⟨hlo, hhi⟩, hcos⟩ := foldPhase_spec q
  rw [← hcos]
  unfold cosPi
  dsimp only
  split
  · exact cosFirstQuadrant_sound hlo (by assumption)
  · rename_i hhalf
    have h := Bounds.neg_sound (cosFirstQuadrant_sound (q := 1 - foldPhase q)
      (by linarith) (by linarith))
    rw [show Real.pi * (↑(1 - foldPhase q) : ℝ) = Real.pi - Real.pi * (foldPhase q : ℝ) by
      push_cast; ring, Real.cos_pi_sub, neg_neg] at h
    exact h

end Legendre.Arithmetic
