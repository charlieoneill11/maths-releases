import HadwigerNelson.Centres.Events.SmallCell
import HadwigerNelson.Centres.Events.HoleCoordinates

/-! Geometry of the midpoint rectangles for the small-chord event. -/

namespace HadwigerNelson.Centres
open Set Placement
noncomputable section

structure SmallPlacement (M U V : Plane) (r t : ℝ) : Prop where
  ux : U 0=M 0-r/2*Real.sin t
  uy : U 1=M 1+r/2*Real.cos t
  vx : V 0=M 0+r/2*Real.sin t
  vy : V 1=M 1-r/2*Real.cos t

theorem placed_midpoint (θ : ℝ) (τ : Translation) (u v ζ : Plane) (t : ℝ) (align : aligned θ t v u) :
    SmallPlacement (place (θ,τ) (midpoint u v)-ζ) (place (θ,τ) u-ζ) (place (θ,τ) v-ζ) (dist u v) t := by
  obtain ⟨hx,hy⟩ := aligned_diagonal align
  have mid (i : Fin 2) : rotate θ (midpoint u v) i = (rotate θ u i+rotate θ v i)/2 := by
    fin_cases i <;> simp [rotate,midpoint] <;> ring
  constructor <;> simp only [place,PiLp.sub_apply,PiLp.add_apply,mid] <;> linarith

namespace SmallCell
variable {W : Wave.Datum} {p : Profile} {l t r : ℝ} {M U V : Plane}

theorem offsets (C : SmallCell W p l t M) (lo : δR≤l) (hi : l≤2/100) (hr : 0≤r) (rmax : r≤2)
    (diag : l^2=4-r^2) :
    |r/2*Real.sin t| ≤ C.tick ∧ 0≤1-r/2*Real.cos t ∧ 1-r/2*Real.cos t≤C.a := by
  have levels := small_levels p lo hi
  have hfrac : 0≤r/2 := by linarith
  have mx : r/2≤1 := by linarith
  have x : |Real.sin t| ≤ C.tick := Real.abs_sin_le_abs.trans C.tick_lower
  have plus : l^2≤(smallUpper p l)^2 := pow_le_pow_left₀ (by linarith [show 0≤δR by norm_num [δR]]) levels.2.2.1 2
  have up : (smallUpper p l)^2 ≤ (2/100:ℝ)^2 :=
    pow_le_pow_left₀ (levels.1.le.trans (levels.2.1.trans levels.2.2.1)) levels.2.2.2 2
  have rad := Real.sq_sqrt (show 0≤1-(smallUpper p l)^2/4 by linarith)
  have root : Real.sqrt (1-(smallUpper p l)^2/4) ≤ r/2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hfrac).mp; nlinarith only [rad,diag,plus]
  have tsq := pow_le_pow_left₀ (abs_nonneg _) C.tick_lower 2
  rw [sq_abs] at tsq
  have one := Real.cos_le_one t
  have gap := mul_le_mul_of_nonneg_right mx (sub_nonneg.mpr one)
  constructor
  · rw [abs_mul,abs_of_nonneg hfrac]
    exact (mul_le_of_le_one_left (abs_nonneg _) mx).trans x
  constructor
  · linarith [mul_le_mul_of_nonneg_left one hfrac]
  · rw [C.a_eq]
    linarith [Real.one_sub_sq_div_two_le_cos (x:=t)]

theorem both_holes (C : SmallCell W p l t M) (F : SmallPlacement M U V r t)
    (off : |r/2*Real.sin t| ≤ C.tick ∧ 0≤1-r/2*Real.cos t ∧ 1-r/2*Real.cos t≤C.a) :
    U-Wave.point 0 1∈Wave.hole W ∧ V-Wave.point 0 (-1)∈Wave.hole W := by
  have My := abs_le.mp C.ordinate.2
  constructor <;> apply in_hole_of_width W (s:=C.y+C.dy+C.a)
  · change |U 0-0|<_ ; rw [F.ux,sub_zero]
    exact (abs_sub _ _).trans_lt (by linarith [C.first_width,off.1])
  · change |U 1-1|≤_ ; rw [F.uy]; exact abs_le.mpr ⟨by linarith [off.2.2], by linarith [off.2.1,C.a_nonneg]⟩
  · change |V 0-0|<_ ; rw [F.vx,sub_zero]
    exact (abs_add_le _ _).trans_lt (by linarith [C.first_width,off.1])
  · change |V 1-(-1)|≤_ ; rw [F.vy]; exact abs_le.mpr ⟨by linarith [off.2.1,C.a_nonneg], by linarith [off.2.2]⟩

theorem tail_bounds (C : SmallCell W p l t M) (F : SmallPlacement M U V r t)
    (off : |r/2*Real.sin t| ≤ C.tick ∧ 0≤1-r/2*Real.cos t ∧ 1-r/2*Real.cos t≤C.a)
    {s : ℝ} (hs : |s|≤w) (T : Plane) (tx : T 0=U 0-Real.sin s) (ty : T 1=U 1-Real.cos s) :
    |T 1-M 1|≤C.b ∧ |T 0|≤1/2 ∧ |T 1|≤1/4 := by
  have sr := Real.abs_sin_le_abs.trans hs
  have sys := pow_le_pow_left₀ (abs_nonneg _) hs 2
  rw [sq_abs] at sys
  have b0 := C.a_nonneg
  have TV : |T 1-M 1|≤C.b := by
    rw [ty,F.uy,C.b_eq]
    exact abs_le.mpr ⟨by linarith [off.2.2,Real.cos_le_one s,sq_nonneg w],
      by linear_combination off.2.1 + Real.one_sub_sq_div_two_le_cos (x:=s) + sys/2 + b0⟩
  refine ⟨TV,?_,?_⟩
  · rw [tx,F.ux]
    calc
      _ ≤ |M 0-r/2*Real.sin t|+|Real.sin s| := abs_sub _ _
      _ ≤ |M 0|+C.tick+w := add_le_add ((abs_sub _ _).trans (add_le_add le_rfl off.1)) sr
      _ ≤ _ := by linarith [C.first_width,width_lt W (C.y+C.dy+C.a),show w≤1/100 by norm_num [w]]
  · calc
      _ = |M 1+(T 1-M 1)| := by ring_nf
      _ ≤ |M 1|+|T 1-M 1| := abs_add_le _ _
      _ ≤ _ := by linarith [C.ordinate.2,C.y_upper,C.b_upper]

theorem tail_sine (C : SmallCell W p l t M) (F : SmallPlacement M U V r t)
    (lo : δR≤l) (hi : l≤2/100) {s : ℝ} (T : Plane) (tx : T 0=U 0-Real.sin s)
    (ty : T 1=U 1-Real.cos s) (hy : |T 1-M 1|≤C.b) (hole : T∈Wave.hole W) :
    |Real.sin (s+t)|<l/2 := by
  have ord : max 0 (C.y-C.b) ≤ |T 1| := by
    apply max_le (abs_nonneg _)
    have e : M 1=T 1+(M 1-T 1) := by ring
    have := abs_add_le (T 1) (M 1-T 1)
    rw [← e,abs_sub_comm (M 1)] at this
    linarith [C.ordinate.1]
  have bound := (hole_width W hole).trans (width_antitone W (a:=max 0 (C.y-C.b)) (b:=T 1)
    (by rwa [abs_of_nonneg (le_max_left 0 _)]))
  have proj : Real.sin (s+t) = -((T 0-M 0)*Real.cos t+(T 1-M 1)*Real.sin t) := by
    rw [Real.sin_add,tx,ty,F.ux,F.uy]; ring
  rw [proj,abs_neg]
  calc
    _ ≤ |(T 0-M 0)*Real.cos t|+|(T 1-M 1)*Real.sin t| := abs_add_le _ _
    _ ≤ (|T 0|+|M 0|)+C.b*C.tick := by
      simp only [abs_mul]
      exact add_le_add ((mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans (abs_sub _ _))
        (mul_le_mul hy (Real.abs_sin_le_abs.trans C.tick_lower) (abs_nonneg _) ((abs_nonneg _).trans hy))
    _ < smallLower p l/2 := by linarith [C.second_width]
    _ ≤ l/2 := by linarith [(small_levels p lo hi).2.1]

end SmallCell
end
end HadwigerNelson.Centres
