import HadwigerNelson.Centres.Events.Widths
import HadwigerNelson.Centres.Events.Medium

namespace HadwigerNelson.Centres.Quadrature

/-- The physical half-width of the midpoint rectangle, before any rounding. -/
noncomputable def exactWidth (W : Wave.Datum) (lo hi t y dy : ℝ) : ℝ :=
  let a := 1-Real.sqrt (1-hi^2/4)+t^2/2
  let b := a+w^2/2
  max 0 (min (Centres.width W (y+dy+a)-t)
    (lo/2-Centres.width W (max 0 (y-b))-b*t))

theorem smallWidth_real (W : Wave.Datum) (p : partialProfile W) (s : Small)
    (guard : rootGuard s.upper = true) (dt : 0≤s.dt) (dy : 0≤s.dy) (j k : Nat) :
    (smallWidth s j k : ℝ) ≤ exactWidth W s.lower s.upper ((j+1:Nat)*s.dt)
      (k*s.dy) s.dy := by
  let t : ℚ := (j+1 : Nat)*s.dt
  let y : ℚ := k*s.dy
  let a : ℚ := deficit s.upper/2+t^2/2
  let b : ℚ := a+unitCone^2/2
  let a₀ : ℝ := 1-Real.sqrt (1-(s.upper:ℝ)^2/4)+(t:ℝ)^2/2
  let b₀ : ℝ := a₀+w^2/2
  have realt : (((j+1:Nat)*s.dt:ℚ):ℝ) = (j+1:Nat)*(s.dt:ℝ) := by push_cast; ring
  have realy : ((k*s.dy:ℚ):ℝ) = (k:ℝ)*(s.dy:ℝ) := by push_cast; ring
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have aa : a₀ ≤ (a:ℝ) := by dsimp [a,a₀]; push_cast; linarith [sag_upper guard]
  have bb : b₀ ≤ (b:ℝ) := by dsimp [b,b₀,unitCone,w]; push_cast; linarith
  have a₀pos : 0≤a₀ := by
    have h : Real.sqrt (1-(s.upper:ℝ)^2/4)≤1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (s.upper:ℝ)])
    dsimp [a₀]; nlinarith [sq_nonneg (t:ℝ)]
  have fy : 0≤(y:ℝ)+(s.dy:ℝ)+a₀ := by positivity
  have up1 : (widthLower (y+s.dy+a):ℝ) ≤ Centres.width W ((y:ℝ)+(s.dy:ℝ)+a₀) := by
    have qa : 0≤a := by exact_mod_cast a₀pos.trans aa
    apply (lower_width W p _ (by positivity)).trans
    apply width_antitone W fy
    push_cast; linarith
  have up2 : Centres.width W (max 0 ((y:ℝ)-b₀)) ≤ (widthUpper (max 0 (y-b)):ℝ) := by
    apply le_trans _ (upper_width W p _ (le_max_left ..))
    apply width_antitone W (by exact_mod_cast (le_max_left 0 (y-b)))
    push_cast
    exact max_le_max_left _ (sub_le_sub_left bb _)
  change ((max 0 (min (widthLower (y+s.dy+a)-t)
      (s.lower/2-widthUpper (max 0 (y-b))-b*t)) : ℚ):ℝ) ≤ _
  rw [←realt,←realy]
  change _ ≤ max 0 (min (Centres.width W ((y:ℝ)+s.dy+a₀)-(t:ℝ))
    ((s.lower:ℝ)/2-Centres.width W (max 0 ((y:ℝ)-b₀))-b₀*(t:ℝ)))
  push_cast
  apply max_le_max_left
  apply min_le_min
  · exact sub_le_sub_right up1 _
  · exact sub_le_sub (sub_le_sub_left up2 _) (mul_le_mul_of_nonneg_right bb (by exact_mod_cast ht))

/-- A passing small-chord check bounds the actual rectangle-area sum after
rotation and translation normalization, using the true sag of the chord. -/
theorem smallPass_real (W : Wave.Datum) (p : partialProfile W) (s : Small)
    (ok : smallPass s = true) :
    (s.target:ℝ) ≤ 8*(s.dt:ℝ)*(s.dy:ℝ)/(Real.pi*W.x)*
      ∑ j : Fin s.angles, ∑ k : Fin s.heights,
        exactWidth W s.lower s.upper ((j.val+1:Nat)*s.dt) (k.val*s.dy) s.dy := by
  simp only [smallPass,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨guard,n⟩,m⟩,lo⟩,_⟩,cap⟩ := ok
  have dt : 0≤s.dt := by unfold Small.dt; apply div_nonneg <;> positivity
  have dy : 0≤s.dy := by unfold Small.dy; positivity
  have hx : 0<W.x := by linarith [W.x_bounds.1]
  have xcast : (((PartialWave.xInt/pic : ℚ):ℝ)) = W.x := by rw [p.1]; norm_num [PartialWave.xInt,pic]
  have h := Rat.cast_le (K:=ℝ) |>.mpr cap
  rw [smallTotal,Rat.cast_div,Rat.cast_mul,Rat.cast_mul,Rat.cast_mul,Rat.cast_mul,
    xcast,cast_array_sum,Rat.cast_ofNat,mul_div_assoc] at h
  simp_rw [cast_array_sum] at h
  refine h.trans ?_
  have sum0 : 0≤∑ j : Fin s.angles, ∑ k : Fin s.heights, (smallWidth s j.val k.val : ℝ) := by
    apply Finset.sum_nonneg; intro j _
    apply Finset.sum_nonneg; intro k _
    exact_mod_cast (show (0:ℚ)≤smallWidth s j.val k.val from le_max_left ..)
  have realDt : 0≤(s.dt:ℝ) := by exact_mod_cast dt
  have realDy : 0≤(s.dy:ℝ) := by exact_mod_cast dy
  calc
    _ = 8*(s.dt:ℝ)*(s.dy:ℝ)/((piHi:ℝ)*W.x)*(∑ j : Fin s.angles,
        ∑ k : Fin s.heights, (smallWidth s j.val k.val:ℝ)) := by ring
    _ ≤ _ := by
      apply mul_le_mul _ (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        smallWidth_real W p s guard dt dy j.val k.val) sum0 (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_right angle_upper hx.le)

def smallCheck : Bool := (Array.range 6).all (fun k => smallPass (small k))

theorem smallCheck_each (ok : smallCheck = true) (k : Fin 6) : smallPass (small k.val) = true := by
  have h := Array.all_eq_true.mp ok k.val (by simp)
  simpa using h

end HadwigerNelson.Centres.Quadrature
