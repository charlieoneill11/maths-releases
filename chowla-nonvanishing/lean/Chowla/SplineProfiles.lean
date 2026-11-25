import Chowla.Splines

namespace Chowla.Spline

open Set MeasureTheory
open scoped BigOperators

/-- Horner interpretation of a rational coefficient list. -/
noncomputable def Coefficients.toReal : Coefficients → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * Coefficients.toReal p x

@[simp] theorem Coefficients.toReal_nil (x : ℝ) : toReal [] x = 0 := rfl

@[simp] theorem Coefficients.toReal_cons (a : ℚ) (p : Coefficients) (x : ℝ) :
    toReal (a :: p) x = (a : ℝ) + x * p.toReal x := rfl

@[simp] theorem Coefficients.toReal_add (p q : Coefficients) (x : ℝ) :
    (add p q).toReal x = p.toReal x + q.toReal x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q =>
      simp only [add, toReal_cons, Rat.cast_add, ih]
      ring

@[simp] theorem Coefficients.toReal_scale (p : Coefficients) (c : ℚ) (x : ℝ) :
    (scale p c).toReal x = (c : ℝ) * p.toReal x := by
  induction p with
  | nil => simp [scale]
  | cons a p ih =>
    simp only [scale, List.map_cons, toReal_cons, Rat.cast_mul] at ih ⊢
    rw [ih]
    ring

@[simp] theorem Coefficients.toReal_translate (p : Coefficients) (c : ℚ) (x : ℝ) :
    (p.translate c).toReal x = p.toReal (x + (c : ℝ)) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change (add [a] (add (0 :: translate p c) (scale (translate p c) c))).toReal x = _
    simp only [toReal_add, toReal_scale, toReal_cons, toReal_nil, Rat.cast_zero,
      mul_zero, add_zero, zero_add, ih]
    ring

private theorem scaleInput_real_aux (p : Coefficients) (c : ℚ) (x : ℝ) (k : ℕ) :
    Coefficients.toReal ((p.zipIdx k).map (fun (a, j) => a * c ^ j)) x =
      (c : ℝ) ^ k * p.toReal ((c : ℝ) * x) := by
  induction p generalizing k with
  | nil => simp
  | cons a p ih =>
    simp only [List.zipIdx_cons, List.map_cons, Coefficients.toReal_cons, Rat.cast_mul,
      Rat.cast_pow, ih, pow_succ]
    ring

@[simp] theorem Coefficients.toReal_scaleInput (p : Coefficients) (c : ℚ) (x : ℝ) :
    (p.scaleInput c).toReal x = p.toReal ((c : ℝ) * x) := by
  simpa [scaleInput] using scaleInput_real_aux p c x 0

private theorem activate_pos_aux (p : Coefficients) (c : ℚ) (x : ℝ)
    (hc : (c : ℝ) ≤ x) (k : ℕ) :
    toReal ((p.zipIdx k).map (fun (a, j) => ⟨c, j, a * j.factorial⟩)) x =
      (x - (c : ℝ)) ^ k * p.toReal (x - (c : ℝ)) := by
  induction p generalizing k with
  | nil => simp
  | cons a p ih =>
    have hcast : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    simp only [List.zipIdx_cons, List.map_cons, toReal_cons, Coefficients.toReal_cons,
      Rat.cast_mul, Rat.cast_natCast, truncatedPower, if_pos hc, ih, pow_succ]
    field_simp

private theorem activate_neg_aux (p : Coefficients) (c : ℚ) (x : ℝ)
    (hc : ¬ (c : ℝ) ≤ x) (k : ℕ) :
    toReal ((p.zipIdx k).map (fun (a, j) => ⟨c, j, a * j.factorial⟩)) x = 0 := by
  induction p generalizing k with
  | nil => simp
  | cons a p ih =>
    simp only [List.zipIdx_cons, List.map_cons, toReal_cons, truncatedPower, if_neg hc,
      ih, mul_zero, add_zero]

theorem activate_sound (p : Coefficients) (c : ℚ) (x : ℝ) :
    (activate p c).toReal x = if (c : ℝ) ≤ x then p.toReal x else 0 := by
  unfold activate
  by_cases hc : (c : ℝ) ≤ x
  · rw [if_pos hc, activate_pos_aux _ _ _ hc, pow_zero, one_mul,
      Coefficients.toReal_translate, sub_add_cancel]
  · rw [if_neg hc, activate_neg_aux _ _ _ hc]

/-- The real interpretation of a polynomial piece agrees pointwise on the half-open interval. -/
theorem piece_sound (p : Coefficients) (lo hi : ℚ) (hle : lo ≤ hi) :
    (piece p lo hi).toReal = (Ico (lo : ℝ) (hi : ℝ)).indicator p.toReal := by
  funext x
  have hle' : (lo : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hle
  simp only [piece, toReal_append, toReal_scale, Rat.cast_neg, Rat.cast_one, activate_sound,
    indicator_apply, mem_Ico]
  by_cases hlo : (lo : ℝ) ≤ x
  · by_cases hhi : (hi : ℝ) ≤ x
    · simp [hlo, hhi, not_lt.mpr hhi]
    · simp [hlo, hhi, lt_of_not_ge hhi]
  · have hhi : ¬ (hi : ℝ) ≤ x := fun h => hlo (hle'.trans h)
    simp [hlo, hhi]

theorem legendreCoefficients_sound (n : ℕ) (x : ℝ) :
    (legendreCoefficients n).1.toReal x = legendre (n := n) x ∧
      (legendreCoefficients n).2.toReal x = (legendrePair x n).2 := by
  induction n with
  | zero => simp [legendreCoefficients, legendre, legendrePair]
  | succ n ih =>
    rcases ih with ⟨hp, hq⟩
    constructor
    · exact hq
    · simp only [legendreCoefficients, legendrePair]
      rcases h₁ : legendreCoefficients n with ⟨p, q⟩
      rcases h₂ : legendrePair x n with ⟨u, v⟩
      simp only [h₁, h₂, Coefficients.toReal_scale, Coefficients.toReal_add,
        Coefficients.toReal_cons, Rat.cast_zero, zero_add] at hp hq ⊢
      rw [hp, hq]
      simp only [legendre, h₂]
      push_cast
      ring

private theorem legendre_sum (cs : Coefficients) (x : ℝ) (k : ℕ) :
    Coefficients.toReal ((cs.zipIdx k).foldr (fun (a, j) p =>
      ((legendreCoefficients (2 * (j + 1))).1.scale a).add p) []) x =
      ∑ i : Fin cs.length, (cs.get i : ℝ) * legendre (2 * (k + i.val + 1)) x := by
  induction cs generalizing k with
  | nil => simp
  | cons a cs ih =>
    let f : Fin (cs.length + 1) → ℝ := fun i =>
      ((a :: cs).get i : ℝ) * legendre (2 * (k + i.val + 1)) x
    change _ = ∑ i, f i
    rw [Fin.sum_univ_succ f]
    simp only [f] at *
    simp only [List.zipIdx_cons, List.foldr_cons, Coefficients.toReal_add,
      Coefficients.toReal_scale, (legendreCoefficients_sound _ x).1, ih, Fin.val_zero, Nat.add_zero, List.get_eq_getElem,
      List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show k + 1 + i.val + 1 = k + (i.val + 1) + 1 by omega]

/-- The exact spline interpretation agrees a.e. with the paper's Legendre profile. -/
theorem legendreProfile_sound (s : ℚ) (cs : Coefficients) (hs : 0 < s) :
    (legendreProfile s cs).toReal =ᵐ[volume]
      Chowla.legendreProfile (s : ℝ) (cs.map (↑)) := by
  unfold legendreProfile
  have hle : -s ≤ s := (neg_nonpos.mpr hs.le).trans hs.le
  rw [piece_sound _ _ _ hle]
  have hne := (volume : Measure ℝ).ae_ne (s : ℝ)
  filter_upwards [hne] with x hx
  have he : x ∈ Ico (-(s : ℝ)) (s : ℝ) ↔ x ∈ Icc (-(s : ℝ)) (s : ℝ) := by
    simp only [mem_Ico, mem_Icc]
    exact and_congr_right (fun _ => lt_iff_le_and_ne.trans (and_iff_left hx))
  rw [Chowla.legendreProfile]
  simp only [Rat.cast_neg, indicator_apply, he]
  split_ifs
  · rw [Coefficients.toReal_scaleInput, legendre_sum, Rat.cast_inv]
    rw [show (s : ℝ)⁻¹ * x = x / (s : ℝ) by ring]
    simp only [Nat.zero_add]
    let e : Fin cs.length ≃ Fin (cs.map (fun a : ℚ => (a : ℝ))).length :=
      finCongr (by simp)
    refine Fintype.sum_equiv e _ _ ?_
    intro i
    simp [e]
  · rfl

end Chowla.Spline
