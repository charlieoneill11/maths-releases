import HadwigerNelson.Stars.RealMoments
import HadwigerNelson.Arithmetic.Magnitude
import Mathlib.Analysis.Complex.Basic

/-! Lower bound for the quantized Fourier magnitude stored by a complete-wave row. -/

namespace HadwigerNelson.Stars.BoxCheck
open Arithmetic MeasureTheory
noncomputable section

private theorem integer_magnitude_le (x y mass err : Int) (n : Nat) (hn : 0 < n) (F H : ℂ)
    (rounded : ‖GaussianInt.value phaseScale ⟨x,y⟩-F‖ ≤
      (mass:ℝ)*(12*(n:ℝ)/(phaseScale:ℝ)))
    (physical : ‖H-Complex.I/(n:ℂ)*F‖ ≤ (err:ℝ)/phaseScale) :
    ((Int.sqrt (x*x+y*y)/(n:Int)-12*mass-err : Int) : ℝ) ≤ (phaseScale:ℝ)*‖H‖ := by
  have S : (0:ℝ) < phaseScale := by norm_num [phaseScale]
  have N : (0:ℝ) < n := by exact_mod_cast hn
  let u := GaussianInt.value phaseScale ⟨x,y⟩
  have hw : (⟨(x:ℝ),(y:ℝ)⟩:ℂ) = (phaseScale:ℂ)*u := by
    apply Complex.ext <;> simp [u,GaussianInt.value,Complex.mul_re,Complex.mul_im] <;> field_simp
  have scaled : ‖(⟨(x:ℝ),(y:ℝ)⟩:ℂ) - (phaseScale:ℂ)*F‖/(n:ℝ) ≤ ((12*mass:Int):ℝ) := by
    rw [hw,←mul_sub,Complex.norm_mul,Complex.norm_intCast,abs_of_pos S]
    calc
      _ ≤ (phaseScale:ℝ)*((mass:ℝ)*(12*(n:ℝ)/phaseScale))/n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left rounded S.le) N.le
      _ = _ := by push_cast; field_simp
  have root := magnitude_sub_allowance x y (n:Int) (12*mass) ((phaseScale:ℂ)*F)
    (by exact_mod_cast hn) (by simpa using scaled)
  simp only [Complex.norm_mul,Complex.norm_intCast,abs_of_pos S,Int.cast_natCast] at root
  have rot : ‖Complex.I/(n:ℂ)*F‖ = ‖F‖/(n:ℝ) := by
    rw [Complex.norm_mul,Complex.norm_div,Complex.norm_I,Complex.norm_natCast]
    ring
  have tri := norm_le_norm_sub_add (Complex.I/(n:ℂ)*F) H
  rw [norm_sub_rev,rot] at tri
  have bound : ‖F‖/(n:ℝ) ≤ (err:ℝ)/phaseScale + ‖H‖ :=
    tri.trans (add_le_add_left physical _)
  have both := mul_le_mul_of_nonneg_left bound S.le
  rw [mul_add,show (phaseScale:ℝ)*((err:ℝ)/phaseScale) = err by field_simp,
    ← mul_div_assoc] at both
  push_cast at root ⊢
  linarith only [both,root]

/-- The executable harmonic is a lower enclosure of the physical angular Fourier magnitude. -/
theorem row_magnitude_lower (k : Fin harmonics) (s : Source) {z : Plane}
    (dom : ResponseDomain s.box s.other z) :
    magnitudeValue k.val (moments arcTable s) ≤ ‖angleMoment (k.val+1) (physicalSigned z s.other)‖ := by
  let spans := runs s.box s.other
  let terms := spans.map (prepareSpan arcTable)
  let x := spanSum terms (fun m => (m.term k.val).re)
  let y := spanSum terms (fun m => (m.term k.val).im)
  let mass := spanSum terms SpanMoments.mass
  let err := spanSum terms SpanMoments.error
  let n := k.val+1
  let a := Int.sqrt (x*x+y*y)/(n:Int)-12*mass-err
  let g := physicalSigned z s.other
  let I : ℂ := ∫ θ in 0..2*Real.pi, (g θ:ℂ)*anglePhase θ^n
  let H : ℂ := ∫ θ in 0..2*Real.pi, ((2*g θ:ℝ):ℂ)*anglePhase θ^n
  have hn : 0 < n := Nat.succ_pos _
  have scaled : (a:ℝ) ≤ (phaseScale:ℝ)*‖H‖ := integer_magnitude_le x y mass err n hn
    (spanEval spans (fun p => exactTerm p n)) H (sum_terms_error arcTable spans k)
    (signed_moment_ticks dom n hn)
  have twice : H = 2*I := by
    dsimp only [H,I]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,mul_assoc]
    exact intervalIntegral.integral_const_mul 2 _
  have S : (0:ℝ) < phaseScale := by norm_num [phaseScale]
  have Q : (0:ℝ) < quant := by norm_num [quant]
  have normed := normalise_sound a 4 (by decide)
  push_cast at normed
  have raw : (normalise a 4:ℝ)/quant ≤ ‖angleMoment n g‖ := by
    apply normed.trans
    apply (div_le_div_of_nonneg_right scaled (show (0:ℝ) ≤ 4*phaseScale*Real.pi by positivity)).trans_eq
    rw [twice,Complex.norm_mul,Complex.norm_ofNat]
    rw [angleMoment_eq_interval,Complex.real_smul,Complex.norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    change (phaseScale:ℝ)*(2*‖I‖)/(4*phaseScale*Real.pi) = (2*Real.pi)⁻¹ * ‖I‖
    field_simp
    ring
  have item : (moments arcTable s).magnitude[k.val]?.getD 0 = max 0 (normalise a 4) := by
    unfold moments momentsFrom
    rw [Array.getElem?_eq_getElem (by simp [k.isLt]), Array.getElem_ofFn]
    rfl
  rw [magnitudeValue,item,Int.cast_max,Int.cast_zero,←max_div_div_right Q.le,zero_div]
  exact max_le (norm_nonneg _) raw

end
end HadwigerNelson.Stars.BoxCheck
