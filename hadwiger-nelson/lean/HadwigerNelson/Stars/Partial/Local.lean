import HadwigerNelson.Stars.Partial.Magnitude
import HadwigerNelson.Stars.Partial.SourceDomain
import HadwigerNelson.Stars.Partial.BoxFamilies
import HadwigerNelson.Stars.Partial.Fourier

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (actualLabel physicalSource quant)
open MeasureTheory
noncomputable section

theorem harmonic_local {d : Nat} (hd : 0<d) (L : Layout.Physical) (k : Fin frequencyCount)
    (φ : Fin d → ℝ) (i : Fin 132621) (z : Plane) (hz : z∈physicalSource (source i.val)) :
    (d:ℝ)/2*harmonicLocal k φ i ≤ angularGain PartialWave.datum φ z := by
  let s := source i.val
  have choose := harmonic_alternate L i
  have legal : 1≤s.other ∧ s.other≤6 ∧ actualLabel 1 ≠ actualLabel s.other := by
    change 1≤(source i.val).other ∧ (source i.val).other≤6 ∧ _ ≠ actualLabel (source i.val).other
    rcases choose with a|a|a <;> rw [a] <;> decide
  have ⟨centre,xrange,inside⟩ := source_domain L ⟨i.val,by omega⟩ hz
  let g := witness s.box s.other
  have lower (t : ℝ) : g t ≤ signedResponse PartialWave.datum z (actualLabel 1) (actualLabel s.other) t := by
    simpa only [response,if_neg (show s.other≠0 by omega),signedResponse] using
      witness_lower s.box s.other (Or.inr legal) z inside xrange t
  exact lower_response_star_bound hd PartialWave.datum φ z (actualLabel 1) (actualLabel s.other)
    centre g (witness_period _ _) (witness_measurable _ _) (witness_norm _ _) lower (k.val+1) _ _
    (mean_witness s {}) (spectrum_witness s (by omega) {} empty_cache_valid k)

theorem native_local {d : Nat} (hd : 0<d) (L : Layout.Physical) (φ : Fin d → ℝ)
    (j : Fin 4122) (z : Plane) (hz : z∈physicalSource (source (132621+j.val))) :
    nativeLocal d j ≤ angularGain PartialWave.datum φ z := by
  let s := source (132621+j.val)
  have zero : s.other=0 := native_alternate L j
  have ⟨centre,xrange,inside⟩ := source_domain L ⟨132621+j.val,by omega⟩ hz
  let f := colourResponse PartialWave.datum z (actualLabel 1)
  let g := witness s.box s.other
  let μ : ℝ := ((row arcTable s {}).2.mean:ℝ)/quant
  have each (t : ℝ) : g t ≤ f t := by
    simpa only [response,if_pos zero,sub_zero] using
      witness_lower s.box s.other (Or.inl zero) z inside xrange t
  have avg : angleMean g ≤ angleMean f := by
    rw [angleMean_eq_interval,angleMean_eq_interval]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact intervalIntegral.integral_mono_on (a:=0) (b:=2*Real.pi) (by positivity)
      (witness_integrable _ _ _ _) (intervalIntegrable_colourResponse ..) (fun t _ => each t)
  have bound := real_native_star_bound hd PartialWave.datum φ z (actualLabel 1) centre μ
    ((mean_witness s {}).trans avg)
  have positive : (0:ℝ)<d := by exact_mod_cast hd
  rw [mul_max_of_nonneg _ _ positive.le,mul_zero,mul_sub,mul_one_div_cancel positive.ne'] at bound
  change max 0 (d*((sourceRow (132621+j.val)).mean:ℝ)/quant-1) ≤ _
  convert bound using 2 <;> dsimp [μ,s,sourceRow] <;> ring

end
end HadwigerNelson.Stars.PartialCheck
