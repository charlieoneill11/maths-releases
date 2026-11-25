import HadwigerNelson.Stars.PhysicalSource
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace HadwigerNelson.Stars.BoxCheck
open MeasureTheory Set
noncomputable section

theorem physicalSource_open (s : Source) : IsOpen (physicalSource s) := by
  have x : Continuous (fun p : Plane => 10^6 * p 0) := continuous_const.mul (PiLp.continuous_apply ..)
  have y : Continuous (fun p : Plane => 10^6 * p 1) := continuous_const.mul (PiLp.continuous_apply ..)
  exact (isOpen_lt continuous_const x).inter ((isOpen_lt x continuous_const).inter
    ((isOpen_lt continuous_const y).inter (isOpen_lt y continuous_const)))

/-- Both side lengths are in millionths of a unit. The source area in the
checker therefore measures real Euclidean area in trillionths. -/
theorem physicalSource_area (s : Source) (hx : s.xlo ≤ s.xhi) (hy : s.ylo ≤ s.yhi) :
    volume.real (physicalSource s) = (s.area : ℝ)/10^12 := by
  let a : Fin 2 → ℝ := ![(s.xlo : ℝ)/10^6,(s.ylo : ℝ)/10^6]
  let b : Fin 2 → ℝ := ![(s.xhi : ℝ)/10^6,(s.yhi : ℝ)/10^6]
  let B := univ.pi fun i => Ioo (a i) (b i)
  have mb : MeasurableSet B := MeasurableSet.pi countable_univ (fun _ _ => measurableSet_Ioo)
  have eq : physicalSource s = (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' B := by
    ext z
    change InSource s (10^6*z 0) (10^6*z 1) ↔
      ∀ i ∈ (univ : Set (Fin 2)), z i ∈ Ioo (a i) (b i)
    constructor
    · rintro ⟨lm,rm,bm,tm⟩ i _
      fin_cases i <;> simp [a,b] <;> constructor <;> linarith
    · intro h
      have u := h 0 trivial
      have v := h 1 trivial
      simp [a,b] at u v
      exact ⟨by linarith [u.1],by linarith [u.2],by linarith [v.1],by linarith [v.2]⟩
  have lo : a ≤ b := by
    intro i
    fin_cases i
    · change (s.xlo : ℝ)/10^6 ≤ (s.xhi : ℝ)/10^6
      exact div_le_div_of_nonneg_right (Int.cast_le.mpr hx) (by positivity)
    · change (s.ylo : ℝ)/10^6 ≤ (s.yhi : ℝ)/10^6
      exact div_le_div_of_nonneg_right (Int.cast_le.mpr hy) (by positivity)
  rw [Measure.real,eq,(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage mb.nullMeasurableSet]
  rw [Real.volume_pi_Ioo_toReal lo,Fin.prod_univ_two]
  simp [a,b,Source.area]
  ring

theorem physical_fourier_weight (s : Source) (hx : s.xlo ≤ s.xhi) (hy : s.ylo ≤ s.yhi) :
    volume.real (physicalSource s)/(Wave.completeDatum.x*Wave.H) =
      2*(s.area : ℝ)/CompleteWave.xInt := by
  rw [physicalSource_area s hx hy,Wave.completeDatum_x]
  norm_num [CompleteWave.scale,Wave.H,CompleteWave.xInt]
  ring

end
end HadwigerNelson.Stars.BoxCheck
