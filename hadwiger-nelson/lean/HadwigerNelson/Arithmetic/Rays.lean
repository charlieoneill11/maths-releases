import HadwigerNelson.Arithmetic.Rounding
import Mathlib.Tactic.FieldSimp

/-! Integer bounds for the rational parametrization of the quarter unit circle. -/

namespace HadwigerNelson.Arithmetic

noncomputable def rayX (t : ℝ) : ℝ := (1-t^2)/(1+t^2)
noncomputable def rayY (t : ℝ) : ℝ := 2*t/(1+t^2)

theorem rayX_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : rayX b ≤ rayX a := by
  apply (div_le_div_iff₀ (by positivity : 0 < 1+b^2) (by positivity : 0 < 1+a^2)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ b+a by linarith)]

theorem rayY_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : rayY a ≤ rayY b := by
  apply (div_le_div_iff₀ (by positivity : 0 < 1+a^2) (by positivity : 0 < 1+b^2)).2
  have hab1 : a*b ≤ 1 :=
    (mul_le_mul_of_nonneg_left hb ha).trans (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab1)]

theorem ray_unit (t : ℝ) : rayX t ^ 2 + rayY t ^ 2 = 1 := by
  dsimp [rayX,rayY]
  have hden : 1+t^2 ≠ 0 := by positivity
  field_simp
  ring

def rayDen (N j : Int) := N*N+j*j
def rayXNum (S N j : Int) := (N*N-j*j)*S
def rayYNum (S N j : Int) := 2*N*j*S

theorem rayDen_pos {N : Int} (j : Int) (hN : 0 < N) : 0 < rayDen N j := by
  unfold rayDen
  nlinarith [sq_nonneg j, mul_pos hN hN]

theorem scaled_rayX (S N j : Int) (hN : 0 < N) :
    (S:ℝ)*rayX ((j:ℝ)/N) = (rayXNum S N j : ℝ) / (rayDen N j : ℝ) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hden : (rayDen N j : ℝ) ≠ 0 := by exact_mod_cast (rayDen_pos j hN).ne'
  dsimp [rayX,rayXNum,rayDen] at *
  push_cast at *
  field_simp

theorem scaled_rayY (S N j : Int) (hN : 0 < N) :
    (S:ℝ)*rayY ((j:ℝ)/N) = (rayYNum S N j : ℝ) / (rayDen N j : ℝ) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hden : (rayDen N j : ℝ) ≠ 0 := by exact_mod_cast (rayDen_pos j hN).ne'
  dsimp [rayY,rayYNum,rayDen] at *
  push_cast at *
  field_simp

/-- Coordinate bounds for an entire coarse or fine half-angle bin. -/
theorem ray_bin_bounds {S N i j : Int} {t : ℝ} (hS : 0 ≤ S) (hN : 0 < N)
    (hi : 0 ≤ i) (hj : j ≤ N) (hlt : (i:ℝ)/N ≤ t) (hrt : t ≤ (j:ℝ)/N) :
    ((rayXNum S N j / rayDen N j : Int) : ℝ) ≤ S*rayX t ∧
    S*rayX t ≤ (ceilDiv (rayXNum S N i) (rayDen N i) : ℝ) ∧
    ((rayYNum S N i / rayDen N i : Int) : ℝ) ≤ S*rayY t ∧
    S*rayY t ≤ (ceilDiv (rayYNum S N j) (rayDen N j) : ℝ) := by
  have hSr : (0:ℝ) ≤ S := by exact_mod_cast hS
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ (i:ℝ)/N := div_nonneg (by exact_mod_cast hi) hNr.le
  have h1 : (j:ℝ)/N ≤ 1 := (div_le_one hNr).2 (by exact_mod_cast hj)
  refine ⟨?_,?_,?_,?_⟩
  · calc
      _ ≤ _ := floorDiv_le_real _ (rayDen_pos j hN)
      _ = _ := (scaled_rayX S N j hN).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (rayX_antitone (h0.trans hlt) hrt) hSr
  · calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (rayX_antitone h0 hlt) hSr
      _ = _ := scaled_rayX S N i hN
      _ ≤ _ := real_le_ceilDiv _ (rayDen_pos i hN)
  · calc
      _ ≤ _ := floorDiv_le_real _ (rayDen_pos i hN)
      _ = _ := (scaled_rayY S N i hN).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (rayY_monotone h0 hlt (hrt.trans h1)) hSr
  · calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (rayY_monotone (h0.trans hlt) hrt h1) hSr
      _ = _ := scaled_rayY S N j hN
      _ ≤ _ := real_le_ceilDiv _ (rayDen_pos j hN)

end HadwigerNelson.Arithmetic
