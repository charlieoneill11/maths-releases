import HadwigerNelson.Wave.Geometry.Cells
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace HadwigerNelson.Wave
open MeasureTheory Set

noncomputable section

theorem cell_measurable (W : Datum) (v : ℝ) : MeasurableSet (cell W v) := by
  have u : Continuous (fun z : Plane => z 0) := PiLp.continuous_apply ..
  have y : Continuous (fun z : Plane => z 1) := PiLp.continuous_apply ..
  exact (u.measurable measurableSet_Ico).inter (y.measurable measurableSet_Ico)

theorem cell_volume (W : Datum) (v : ℝ) (_hv : 0 ≤ v) :
    volume (cell W v) = ENNReal.ofReal (2*W.x*v) := by
  let edge : Fin 2 → ℝ := ![2*W.x,v]
  let box : Set (Fin 2 → ℝ) := univ.pi fun i => Ico 0 (edge i)
  have mb : MeasurableSet box := MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico
  have eq : cell W v = (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' box := by
    ext p
    change _ ↔ ∀ i ∈ (univ : Set (Fin 2)), p i ∈ Ico 0 (edge i)
    constructor
    · intro hp i _
      fin_cases i
      · exact hp.1
      · exact hp.2
    · intro h
      exact ⟨h 0 trivial,h 1 trivial⟩
  rw [eq,(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage mb.nullMeasurableSet]
  have formula := Real.volume_pi_Ico (a:=(0:Fin 2 → ℝ)) (b:=edge)
  change volume (univ.pi fun i => Ico ((0 : Fin 2 → ℝ) i) (edge i)) = _
  rw [formula,Fin.prod_univ_two]
  simp [edge,ENNReal.ofReal_mul,show 0 ≤ 2*W.x by linarith [W.x_bounds.1]]

theorem lattice_covolume (W : Datum) : volume (cell W (3*H)) = ENNReal.ofReal (6*W.x*H) := by
  rw [cell_volume W (3*H) (by linarith [H_pos])]
  congr 1
  ring

theorem holeLattice_covolume (W : Datum) : volume (cell W H) = ENNReal.ofReal (2*W.x*H) :=
  cell_volume W H H_pos.le

end
end HadwigerNelson.Wave
