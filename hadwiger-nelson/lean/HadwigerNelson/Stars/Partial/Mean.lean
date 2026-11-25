import HadwigerNelson.Stars.Partial.Integral
import HadwigerNelson.Stars.Partial.Lengths
import HadwigerNelson.Stars.Partial.Spans
import HadwigerNelson.Stars.MomentSums

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Span source spanArc endpoint spanEval changeOf)
open MeasureTheory
noncomputable section

theorem mean_integral (src : Angular.Box) (other : Nat) :
    (meanTicks arcTable (runs src other):ℝ) ≤
      (scale:ℝ)*(∫ θ in 0..2*Real.pi, witness src other θ) := by
  let ss := runs src other
  let length (p : Span) := endpoint p.quadrant p.stop-endpoint p.quadrant p.start
  have integral := witness_integral src other (fun _ => (1:ℝ)) continuous_const
  simp only [smul_eq_mul,mul_one] at integral
  have eval (p : Span) : changeOf (primitive (fun _ => (1:ℝ))) p = (p.coeff:ℝ)*length p := by
    simp [primitive,changeOf,smul_eq_mul,length,mul_sub]
  rw [integral,BoxCheck.spanEval_fin,Finset.mul_sum]
  unfold meanTicks
  rw [BoxCheck.array_sum_by,Int.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  let p := ss[i.val]
  have valid := runs_valid src other p (Array.getElem_mem _)
  have bounds := spanArc_bounds p valid.2.1 valid.2.2.1
  have low := Arithmetic.signed_arc_lower p.coeff (spanArc arcTable p).low
    (spanArc arcTable p).high ((scale:ℝ)*length p) bounds.1 bounds.2
  rw [eval]
  change _ ≤ (scale:ℝ)*((p.coeff:ℝ)*length p)
  exact low.trans_eq (by ring)

theorem mean_witness (s : BoxCheck.Source) (cache : Cache) :
    ((row arcTable s cache).2.mean:ℝ)/BoxCheck.quant ≤ angleMean (witness s.box s.other) := by
  have lo := mean_integral s.box s.other
  have pos : (0:ℝ)<(2:ℝ)*(scale:ℝ)*Real.pi := by unfold scale;positivity
  apply (normalized_le _).trans
  apply (div_le_div_of_nonneg_right lo pos.le).trans_eq
  rw [angleMean_eq_interval]
  unfold scale
  push_cast
  field_simp

end
end HadwigerNelson.Stars.PartialCheck
