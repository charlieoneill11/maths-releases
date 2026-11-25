import HadwigerNelson.Arithmetic.Rounding
import Mathlib.Tactic.FieldSimp

/-! Restriction, translation, and endpoint enclosures for the piecewise-affine profiles. -/

namespace HadwigerNelson.Arithmetic

theorem linearAt_left (l r u v : ℝ) : linearAt l u r v l = u := by simp [linearAt]

theorem linearAt_right {l r : ℝ} (u v : ℝ) (hlr : l < r) :
    linearAt l u r v r = v := by
  simp [linearAt,(sub_pos.mpr hlr).ne']

theorem linearAt_sub (l r u v x d : ℝ) :
    linearAt l (u-d) r (v-d) x = linearAt l u r v x - d := by
  dsimp [linearAt]
  ring

/-- Rounding up both endpoints rounds up the entire closed segment. -/
theorem linearAt_mono {l r x a b u v : ℝ} (hlr : l < r) (hl : l ≤ x) (hr : x ≤ r)
    (ha : a ≤ u) (hb : b ≤ v) : linearAt l a r b x ≤ linearAt l u r v x := by
  have hden := sub_pos.mpr hlr
  dsimp [linearAt]
  rw [← le_sub_iff_add_le', div_le_iff₀ hden]
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hr),
    mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hl)]

/-- Reconstruct a segment from any two distinct height samples on the same affine line. -/
theorem linearAt_restrict {l r s t : ℝ} (u v z : ℝ) (hlr : l < r) (hst : s < t) :
    linearAt s (linearAt l u r v s) t (linearAt l u r v t) z = linearAt l u r v z := by
  dsimp [linearAt]
  have hden := (sub_pos.mpr hlr).ne'
  have hseg := (sub_pos.mpr hst).ne'
  field_simp
  ring

theorem linearAt_clipped_upper (l r u v d s : Int) {z : ℝ}
    (hlr : l < r) (hsr : s < r) (hsz : (s:ℝ) ≤ z) (hzr : z ≤ (r:ℝ)) :
    linearAt l u r v z - d ≤ linearAt s (interpUp l u r v s - d) r (v-d) z := by
  have hlr' : (l:ℝ) < r := by exact_mod_cast hlr
  have hsr' : (s:ℝ) < r := by exact_mod_cast hsr
  rw [← linearAt_restrict (s := (s:ℝ)) (t := (r:ℝ)) _ _ _ hlr' hsr',
    linearAt_right _ _ hlr', ← linearAt_sub]
  exact linearAt_mono hsr' hsz hzr (sub_le_sub_right (interpUp_spec _ _ _ _ _ hlr) _) le_rfl

end HadwigerNelson.Arithmetic
