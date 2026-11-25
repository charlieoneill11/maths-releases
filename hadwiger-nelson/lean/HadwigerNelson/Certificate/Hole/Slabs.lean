import HadwigerNelson.Certificate.Hole.Runtime
import HadwigerNelson.Arithmetic.Rounding
import HadwigerNelson.Wave.Holes.Definitions

namespace HadwigerNelson.Certificate.Hole

private theorem real_floor_div (a b : ℤ) (h : 0<b) : ⌊(a:ℝ)/b⌋ = a/b :=
  Int.floor_eq_iff.mpr ⟨Arithmetic.floorDiv_le_real a h,Arithmetic.real_lt_floorDiv_add_one a h⟩

/-- The downward-rounded integral of the positive part of one chord, in
twice square-picounits. Mixed signs use the area of a triangle. -/
theorem segment_eq (u v w : ℤ) :
    Wave.areaDown ((w:ℝ)/10^12 *
      Wave.positiveChord ((u:ℝ)/10^12) ((v:ℝ)/10^12)) =
    (segment u v w : ℝ)/(2*10^24) := by
  unfold Wave.areaDown Wave.positiveChord segment
  have su : 0 ≤ (u:ℝ)/10^12 ↔ 0 ≤ u := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<10^12),zero_mul]
    exact_mod_cast Iff.rfl
  have sv : 0 ≤ (v:ℝ)/10^12 ↔ 0 ≤ v := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<10^12),zero_mul]
    exact_mod_cast Iff.rfl
  simp only [su,sv]
  split_ifs with hu hv hv
  · rw [show 2*((w:ℝ)/10^12*((u/10^12+v/10^12)/2))*10^24 = (w*(u+v):ℤ) by push_cast; ring,
      Int.floor_intCast]
  · have z : (0:ℝ)<u-v := by exact_mod_cast (show 0<u-v by omega)
    have eq : 2*((w:ℝ)/10^12*((u/10^12)^2/(2*(u/10^12-v/10^12))))*10^24 =
        ((w*u^2:ℤ):ℝ)/(u-v:ℤ) := by
      push_cast
      field_simp
    rw [eq,real_floor_div _ _ (by omega)]
  · have z : (0:ℝ)<v-u := by exact_mod_cast (show 0<v-u by omega)
    have eq : 2*((w:ℝ)/10^12*((v/10^12)^2/(2*(v/10^12-u/10^12))))*10^24 =
        ((w*v^2:ℤ):ℝ)/(v-u:ℤ) := by
      push_cast
      field_simp
    rw [eq,real_floor_div _ _ (by omega)]
  · norm_num

theorem ticks_eq (dx dy : ℤ) (hy : dy<2*cutoff) :
    ticks dx dy = ∑ i : Fin 68, slab dx dy i.val := by
  simp only [ticks,if_neg (not_le.mpr hy)]
  rw [← Array.sum_toList,Array.toList_ofFn,List.sum_ofFn]

end HadwigerNelson.Certificate.Hole
