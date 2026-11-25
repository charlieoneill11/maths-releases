import HadwigerNelson.Stars.Partial.Mean
import HadwigerNelson.Stars.Partial.Power
import HadwigerNelson.Stars.RealFourier.Primitive
import Mathlib.Analysis.Complex.Basic

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Span endpoint exactTerm spanEval)
open Arithmetic MeasureTheory
noncomputable section

theorem fourier_integral (src : Angular.Box) (other k : Nat) (hk : 0<k) :
    (∫ θ in 0..2*Real.pi, (witness src other θ:ℂ)*anglePhase θ^k) =
      Complex.I/(k:ℂ)*spanEval (runs src other) (fun p => exactTerm p k) := by
  let f (t : ℝ) := anglePhase t^k
  have hf : Continuous f := anglePhase_continuous.pow k
  have eq := witness_integral src other f hf
  change (∫ θ in 0..2*Real.pi, witness src other θ • f θ) = _
  refine eq.trans ?_
  rw [BoxCheck.spanEval_fin,BoxCheck.spanEval_fin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let p := (runs src other)[i.val]
  have valid := runs_valid src other p (Array.getElem_mem i.isLt)
  have diff : (∫ t in 0..endpoint p.quadrant p.stop, f t) -
      (∫ t in 0..endpoint p.quadrant p.start, f t) =
      ∫ t in endpoint p.quadrant p.start..endpoint p.quadrant p.stop, f t := by
    rw [←intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 (endpoint p.quadrant p.start)) (hf.intervalIntegrable _ (endpoint p.quadrant p.stop))]
    abel
  change BoxCheck.changeOf (primitive f) p = Complex.I/(k:ℂ)*exactTerm p k
  change (p.coeff:ℂ)*(∫ θ in 0..endpoint p.quadrant p.stop,f θ) -
    (p.coeff:ℂ)*(∫ θ in 0..endpoint p.quadrant p.start,f θ) = _
  rw [←mul_sub,diff,integral_anglePhase_pow _ _ _ hk,BoxCheck.endpoint_phase _ _ valid.1,BoxCheck.endpoint_phase _ _ valid.1]
  unfold exactTerm
  ring

private theorem unit_round (z : GaussianInt) (mass n : Nat) (hn : 0<n) (F : ℂ)
    (rounded : ‖GaussianInt.value scale z-F‖ ≤ mass*(12*(n:ℝ)/(scale:ℝ))) :
    ((Int.sqrt (z.re*z.re+z.im*z.im)/(n:Int)-12*(mass:Int) : Int):ℝ) ≤
      (scale:ℝ)*‖Complex.I/(n:ℂ)*F‖ := by
  have S : (0:ℝ)<scale := by norm_num [scale]
  have N : (0:ℝ)<n := by exact_mod_cast hn
  have coord : (⟨(z.re:ℝ),(z.im:ℝ)⟩:ℂ) = (scale:ℂ)*GaussianInt.value scale z := by
    apply Complex.ext <;> simp [GaussianInt.value,Complex.mul_re,Complex.mul_im] <;> field_simp
  have scaled : ‖(⟨(z.re:ℝ),(z.im:ℝ)⟩:ℂ)-(scale:ℂ)*F‖/(n:ℝ) ≤ ((12*(mass:Int):Int):ℝ) := by
    rw [coord,←mul_sub,norm_mul,Complex.norm_intCast,abs_of_pos S]
    apply (div_le_iff₀ N).2
    calc
      _ ≤ (scale:ℝ)*((mass:ℝ)*(12*(n:ℝ)/(scale:ℝ))) := mul_le_mul_of_nonneg_left rounded S.le
      _ = _ := by push_cast; field_simp
  have root := magnitude_sub_allowance z.re z.im (n:Int) (12*(mass:Int)) ((scale:ℂ)*F)
    (by exact_mod_cast hn) (by simpa using scaled)
  rw [Complex.norm_mul,Complex.norm_intCast,abs_of_pos S,Int.cast_natCast] at root
  apply root.trans_eq
  rw [Complex.norm_mul,Complex.norm_div,Complex.norm_I,Complex.norm_natCast]
  ring

theorem spectrum_witness (s : BoxCheck.Source) (harm : s.other≠0) (cache : Cache)
    (valid : ValidCache cache) (k : Fin frequencyCount) :
    (((row arcTable s cache).2.spectrum[k.val]?.getD 0):ℝ)/BoxCheck.quant ≤
      ‖angleMoment (k.val+1) (witness s.box s.other)‖ := by
  let n := k.val+1
  let ss := runs s.box s.other
  let ts := ss.map uncached
  let z := sumTerms ts k.val
  let num : Int := Int.sqrt (z.re*z.re+z.im*z.im)/(n:Int)-12*ss.size
  let F := spanEval ss (fun p => exactTerm p n)
  let g := witness s.box s.other
  have hn : 0<n := Nat.succ_pos _
  have E := sum_error s.box s.other k
  have round : (num:ℝ) ≤ (scale:ℝ)*‖Complex.I/(n:ℂ)*F‖ := unit_round z ss.size n hn F E
  have integral := fourier_integral s.box s.other n hn
  have R := prepare_true ss cache valid
  have hneed : (s.other != 0) = true := bne_iff_ne.mpr harm
  have item : (row arcTable s cache).2.spectrum[k.val]?.getD 0 = normalized (max 0 num) := by
    simp only [row,hneed,beq_iff_eq,harm,if_false]
    simp only [Array.getElem?_ofFn,k.isLt,dif_pos,Option.getD_some]
    change magnitude (prepare true ss cache).2 k.val = _
    rw [R.2]
    simp only [magnitude,Array.size_map]
    rfl
  rw [item]
  apply (normalized_le _).trans
  have S : (0:ℝ)<scale := by norm_num [scale]
  have P : 0<2*(scale:ℝ)*Real.pi := by positivity
  have nonneg : 0≤(scale:ℝ)*‖Complex.I/(n:ℂ)*F‖ := by positivity
  have both := max_le nonneg round
  rw [Int.cast_max,Int.cast_zero]
  apply (div_le_div_of_nonneg_right both P.le).trans_eq
  have normEq : ‖angleMoment n g‖ = (2*Real.pi)⁻¹*‖Complex.I/(n:ℂ)*F‖ := by
    rw [angleMoment_eq_interval,Complex.real_smul,Complex.norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact congrArg (fun z : ℂ => (2*Real.pi)⁻¹*‖z‖) integral
  change (scale:ℝ)*‖Complex.I/(n:ℂ)*F‖/(2*(scale:ℝ)*Real.pi) = ‖angleMoment n g‖
  rw [normEq]
  field_simp

end
end HadwigerNelson.Stars.PartialCheck
