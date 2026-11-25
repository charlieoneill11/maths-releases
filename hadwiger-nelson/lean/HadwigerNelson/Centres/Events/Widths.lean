import HadwigerNelson.Centres.Events.Definitions
import HadwigerNelson.Centres.Events.Runtime
import HadwigerNelson.Certificate.Hole.Width

namespace HadwigerNelson.Centres.Quadrature
open Certificate.Hole (cutoff)
open Set

theorem width_nonneg (W : Wave.Datum) (z : ℝ) : 0 ≤ Centres.width W z := by
  unfold Centres.width
  split <;> first | exact (W.left_bounds _).1 | rfl

theorem width_antitone (W : Wave.Datum) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Centres.width W b ≤ Centres.width W a := by
  simp only [Centres.width,abs_of_nonneg ha,abs_of_nonneg (ha.trans hab)]
  by_cases hb : b≤W.y0
  · rw [if_pos hb,if_pos (hab.trans hb)]
    have ht : W.y0 ≤ Wave.H/2 := by linarith [W.y0_bounds.2,Wave.H_pos]
    exact W.left_antitone ⟨ha,(hab.trans hb).trans ht⟩ ⟨ha.trans hab,hb.trans ht⟩ hab
  · rw [if_neg hb]
    split <;> first | exact (W.left_bounds _).1 | rfl

theorem width_at_cutoff (W : Wave.Datum) {z : ℝ} (hz : W.y0 ≤ z) :
    Centres.width W z = 0 := by
  rw [Centres.width,abs_of_nonneg (W.y0_bounds.1.trans hz)]
  split_ifs with h
  · have e := le_antisymm h hz
    subst z
    exact W.left_zero _ ⟨le_rfl,by linarith [W.y0_bounds.2,Wave.H_pos]⟩
  · rfl

private theorem width_outside (t : ℤ) (ht : cutoff ≤ t) : Certificate.Hole.width t = 0 := by
  unfold Certificate.Hole.width
  apply if_pos
  change 9180000000 ≤ t.natAbs
  have h : 9180000000 ≤ t := ht
  have n : (t.natAbs : ℤ) = t := by rw [Int.natCast_natAbs,abs_of_nonneg (by omega)]
  omega

private theorem exact_floor (W : Wave.Datum) (p : partialProfile W) (t : ℤ) (ht : 0≤t) :
    Certificate.Hole.width t = ⌊Centres.width W ((t:ℝ)/10^12)*10^12⌋ := by
  by_cases low : t≤cutoff
  · rw [Certificate.Hole.width_floor W p t (by rwa [abs_of_nonneg ht])]
    have nn : 0 ≤ (t:ℝ)/10^12 := by positivity
    have upper : (t:ℝ)/10^12 ≤ W.y0 := by
      rw [p.2.1]
      change t ≤ 9180000000 at low
      have c : (t:ℝ)≤9180000000 := by exact_mod_cast low
      linarith
    simp only [Centres.width,abs_of_nonneg nn,if_pos upper]
  · have upper : W.y0 ≤ (t:ℝ)/10^12 := by
      rw [p.2.1]
      change ¬t ≤ 9180000000 at low
      have c : (9180000000:ℝ)≤t := by exact_mod_cast (show (9180000000:ℤ)≤t by omega)
      linarith
    rw [width_outside t (le_of_not_ge low),width_at_cutoff _ upper,zero_mul,Int.floor_zero]

private theorem cast_tick (y : ℚ) : ((y*pic:ℚ):ℝ) = (y:ℝ)*10^12 := by norm_num [pic]

private theorem ceil_ident (z : ℚ) : z.ceil = ⌈z⌉ := by
  rw [Rat.ceil_eq_neg_floor_neg]; rfl

theorem lower_width (W : Wave.Datum) (p : partialProfile W) (y : ℚ) (hy : 0≤y) :
    (widthLower y : ℝ) ≤ Centres.width W y := by
  let t : ℤ := (y*pic).ceil
  have nn : 0 ≤ t := by dsimp [t]; rw [ceil_ident]; apply Int.ceil_nonneg; positivity
  have bound : (y:ℝ)*10^12 ≤ t := by
    rw [← cast_tick]
    dsimp [t]; rw [ceil_ident]; exact_mod_cast (Int.le_ceil (y*pic))
  have w := width_antitone W (by exact_mod_cast hy) (show (y:ℝ)≤(t:ℝ)/10^12 by linarith)
  simp only [widthLower,Rat.cast_div,Rat.cast_intCast,pic,Rat.cast_pow,Rat.cast_ofNat]
  change (Certificate.Hole.width t : ℝ)/10^12 ≤ _
  have floor := Int.floor_le (Centres.width W ((t:ℝ)/10^12)*10^12)
  rw [← exact_floor W p t nn] at floor
  linarith

theorem upper_width (W : Wave.Datum) (p : partialProfile W) (y : ℚ) (hy : 0≤y) :
    Centres.width W y ≤ (widthUpper y : ℝ) := by
  let t : ℤ := (y*pic).floor
  have nn : 0 ≤ t := by change 0≤⌊y*pic⌋; apply Int.floor_nonneg.mpr; positivity
  have bound : (t:ℝ) ≤ (y:ℝ)*10^12 := by
    rw [← cast_tick]
    exact_mod_cast (Int.floor_le (y*pic))
  have w := width_antitone W (by positivity : 0 ≤ (t:ℝ)/10^12)
    (show (t:ℝ)/10^12≤y by linarith)
  by_cases out : cutoff≤t
  · have h : W.y0≤(y:ℝ) := by
      rw [p.2.1]
      change 9180000000≤t at out
      have c : (9180000000:ℝ)≤t := by exact_mod_cast out
      linarith
    rw [width_at_cutoff W h,widthUpper,if_pos out]
    norm_num
  · rw [widthUpper,if_neg out]
    have floor := Int.lt_floor_add_one (Centres.width W ((t:ℝ)/10^12)*10^12)
    rw [←exact_floor W p t nn] at floor
    simp only [Rat.cast_div,Rat.cast_add,Rat.cast_intCast,Rat.cast_one,pic,Rat.cast_pow,Rat.cast_ofNat]
    change _ ≤ ((Certificate.Hole.width t : ℝ)+1)/10^12
    linarith

end HadwigerNelson.Centres.Quadrature
