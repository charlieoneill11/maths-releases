import HadwigerNelson.Forest.Rotations
import HadwigerNelson.Placement.AngularIntegral
import HadwigerNelson.Placement.Quadrants
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Function.Floor

namespace HadwigerNelson.Forest
open MeasureTheory Set Placement Arithmetic
open scoped BigOperators
noncomputable section

/-- The folded half-angle bin depends only on the unsigned sine and cosine. -/
def foldedIndex (N : ℕ) (θ : ℝ) : ℕ :=
  min (N-1) ⌊(N:ℝ)*|Real.sin θ|/(1+|Real.cos θ|)⌋₊

private theorem foldedIndex_measurable (N : ℕ) : Measurable (foldedIndex N) := by
  unfold foldedIndex
  fun_prop

private theorem foldedIndex_pi (N : ℕ) (θ : ℝ) : foldedIndex N (θ+Real.pi)=foldedIndex N θ := by
  simp [foldedIndex]
private theorem foldedIndex_mirror (N : ℕ) (θ : ℝ) : foldedIndex N (Real.pi-θ)=foldedIndex N θ := by
  simp [foldedIndex]

private theorem open_bin {N j : ℕ} (hn : 0<N) (hj : j<N) {θ : ℝ}
    (hθ : θ∈Ioo (binEdge N j) (binEdge N (j+1))) : foldedIndex N θ=j := by
  let lo := (j:ℝ)/N
  let hi := ((j+1:ℕ):ℝ)/N
  have hn' : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
  have lo0 : 0≤lo := div_nonneg (Nat.cast_nonneg _) hn'.le
  have hi1 : hi≤1 := (div_le_one hn').mpr (by exact_mod_cast Nat.succ_le_of_lt hj)
  have small : θ/2∈Ioo (Real.arctan lo) (Real.arctan hi) := by
    obtain ⟨low,up⟩ := hθ
    change 2*Real.arctan lo<θ at low
    change θ<2*Real.arctan hi at up
    exact ⟨by linarith,by linarith⟩
  let u := Real.tan (θ/2)
  have angle : Real.arctan u=θ/2 := Real.arctan_tan
    (by linarith [small.1,Real.arctan_nonneg.mpr lo0,Real.pi_pos])
    (by have up := Real.arctan_mono hi1; rw [Real.arctan_one] at up; linarith [small.2,Real.pi_pos])
  obtain ⟨low,high⟩ : lo<u ∧ u<hi := by
    rw [← angle] at small
    exact ⟨Real.arctan_lt_arctan_iff.mp small.1,Real.arctan_lt_arctan_iff.mp small.2⟩
  have u0 := lo0.trans low.le
  have u1 := high.le.trans hi1
  have sin : Real.sin θ = rayY u := by convert sin_two_arctan u using 2; linarith
  have cos : Real.cos θ = rayX u := by convert cos_two_arctan u using 2; linarith
  have posY : 0≤rayY u := div_nonneg (by positivity) (by positivity)
  have posX : 0≤rayX u := div_nonneg (by nlinarith [mul_nonneg (sub_nonneg.mpr u1) (add_nonneg zero_le_one u0)]) (by positivity)
  have eq : (N:ℝ)*rayY u/(1+rayX u) = N*u := by
    have denom : 1+rayX u = 2/(1+u^2) := by unfold rayX; field_simp; ring
    rw [denom,rayY]; field_simp
  have floor : ⌊(N:ℝ)*u⌋₊=j := (Nat.floor_eq_iff (mul_nonneg hn'.le u0)).mpr ⟨by
    have z := (div_lt_iff₀ hn').mp low
    linarith,by
    have z := (lt_div_iff₀ hn').mp high
    push_cast at z; linarith⟩
  simp only [foldedIndex,sin,cos,abs_of_nonneg posY,abs_of_nonneg posX,eq,floor,min_eq_right (by omega : j≤N-1)]

/-- Exact mean of a folded step function, with no conditions on the signs
of its finitely many cell values. Endpoints of bins have measure zero. -/
theorem folded_mean (N : ℕ) (hn : 0<N) (c : ℕ → ℝ) (φ : ℝ) :
    (∫ θ,c (foldedIndex N (θ+φ)) ∂uniformInterval (2*Real.pi)) =
      2/Real.pi * ∑ i∈Finset.range N,c i*(binEdge N (i+1)-binEdge N i) := by
  let f (θ : ℝ) := c (foldedIndex N θ)
  have per : Function.Periodic f (2*Real.pi) := fun θ => by simp [f,foldedIndex]
  have meas : Measurable f := (measurable_of_countable c).comp (foldedIndex_measurable N)
  have int (a b : ℝ) : IntervalIntegrable f volume a b := by
    apply intervalIntegrable_iff.mpr
    apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne meas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro θ
    exact Finset.single_le_sum (f:=fun i => ‖c i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr ((min_le_left _ _).trans_lt (Nat.sub_lt hn (by decide : 0<1))))
  have edges (j : ℕ) (hj : j<N) :
      (∫ θ in binEdge N j..binEdge N (j+1),f θ) = c j*(binEdge N (j+1)-binEdge N j) := by
    calc _ = ∫ _ in binEdge N j..binEdge N (j+1),c j := by
           apply intervalIntegral.integral_congr_ae
           filter_upwards [show ∀ᵐ (θ:ℝ) ∂volume, θ≠binEdge N (j+1) from
             volume.ae_ne _] with θ ne ht
           rw [uIoc_of_le (binEdge_mono N j)] at ht
           exact congrArg c (open_bin hn hj ⟨ht.1,lt_of_le_of_ne ht.2 ne⟩)
         _ = _ := by simp [mul_comm]
  have first : binEdge N 0=0 := by simp [binEdge]
  have last : binEdge N N=Real.pi/2 := by simp [binEdge,hn.ne',Real.arctan_one]; ring
  have sum : (∫ θ in 0..Real.pi/2,f θ) = ∑ i∈Finset.range N,c i*(binEdge N (i+1)-binEdge N i) := by
    rw [← first,← last,← intervalIntegral.sum_integral_adjacent_intervals (fun j _ => int (binEdge N j) (binEdge N (j+1)))]
    exact Finset.sum_congr rfl (fun j hj => edges j (Finset.mem_range.mp hj))
  change (∫ θ,f (θ+φ) ∂uniformInterval (2*Real.pi))=_
  rw [integral_uniformInterval (by positivity),intervalIntegral.integral_comp_add_right]
  have shift := per.intervalIntegral_add_eq φ 0
  simp only [zero_add] at shift
  rw [zero_add,add_comm (2*Real.pi) φ,shift]
  rw [integral_four_quadrants f int (fun θ => congrArg c (foldedIndex_pi N θ)) (fun θ => congrArg c (foldedIndex_mirror N θ)),sum]
  ring

/-- A fixed nonzero vector determines one angular offset for its entire orbit. -/
theorem rotated_components (v : Plane) : ∃ φ : ℝ, ∀ θ,
    rotate θ v = Wave.point (‖v‖*Real.cos (θ+φ)) (‖v‖*Real.sin (θ+φ)) := by
  let z : ℂ := ⟨v 0,v 1⟩
  have hn : ‖z‖=‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm,Complex.normSq_apply]
    simpa [z,pow_two] using (coord_dist_sq v 0).symm
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  rw [hn] at hc hs
  refine ⟨z.arg,fun θ => ?_⟩
  ext i
  fin_cases i
  · change Real.cos θ*v 0 - Real.sin θ*v 1 = ‖v‖*Real.cos (θ+z.arg)
    rw [Real.cos_add]
    change ‖v‖*Real.cos z.arg=v 0 at hc
    change ‖v‖*Real.sin z.arg=v 1 at hs
    linear_combination -Real.cos θ*hc + Real.sin θ*hs
  · change Real.sin θ*v 0 + Real.cos θ*v 1 = ‖v‖*Real.sin (θ+z.arg)
    rw [Real.sin_add]
    change ‖v‖*Real.cos z.arg=v 0 at hc
    change ‖v‖*Real.sin z.arg=v 1 at hs
    linear_combination -Real.sin θ*hc - Real.cos θ*hs

end
end HadwigerNelson.Forest
