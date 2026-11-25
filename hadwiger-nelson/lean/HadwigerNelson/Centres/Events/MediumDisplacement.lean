import HadwigerNelson.Centres.Events.Medium
import HadwigerNelson.Centres.Events.Definitions
import HadwigerNelson.Forest.Rotations

namespace HadwigerNelson.Centres
open Wave Placement
noncomputable section

/-- Rectangle containing the physical displacement in one angular bin.
The upper chord endpoint determines its sag and the angular endpoint
determines the transverse excursion. -/
theorem medium_displacement_bounds {q : ℚ} (root : Quadrature.rootGuard q = true)
    {θ t T : ℝ} {v u : Plane} (align : aligned θ t v u) (ht : |t| ≤ T)
    (dist2 : dist u v≤2) (ch : chord u v ≤ (q:ℝ)) :
    |(rotate θ (u-v)-point 0 2) 0|≤2*T ∧
    |(rotate θ (u-v)-point 0 2) 1|≤(Quadrature.deficit q:ℝ)+T^2 := by
  rw [align]
  simp only [PiLp.sub_apply,PiLp.smul_apply,point_fst,point_snd,smul_eq_mul,sub_zero,abs_mul,abs_neg,
    abs_of_nonneg dist_nonneg]
  have ds := dist_nonneg (x:=u) (y:=v)
  refine ⟨mul_le_mul dist2 (Real.abs_sin_le_abs.trans ht) (abs_nonneg _) (by norm_num),?_⟩
  have cn : 0≤chord u v := Real.sqrt_nonneg _
  have sq : (chord u v)^2 = 4-dist u v^2 := Real.sq_sqrt (by nlinarith)
  have qn := (Quadrature.rootGuard_sound root).1
  have ex : Real.sqrt (4-(q:ℝ)^2) ≤ dist u v := by
    exact Real.sqrt_le_iff.mpr ⟨ds,by nlinarith [pow_le_pow_left₀ cn ch 2]⟩
  have upper : dist u v*Real.cos t≤2 :=
    (mul_le_mul_of_nonneg_left (Real.cos_le_one t) ds).trans (by simpa using dist2)
  rw [abs_of_nonpos (sub_nonpos.mpr upper)]
  have co := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x:=t)) ds
  have ts : t^2≤T^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  nlinarith [Quadrature.deficit_upper root,mul_nonneg (sub_nonneg.mpr dist2) (sq_nonneg t)]

end
end HadwigerNelson.Centres
