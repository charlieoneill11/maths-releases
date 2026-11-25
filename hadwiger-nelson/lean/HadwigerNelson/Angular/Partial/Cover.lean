import HadwigerNelson.Angular.Partial.Clipped
import HadwigerNelson.Angular.Partial.Weights
import HadwigerNelson.Angular.PhysicalBox

namespace HadwigerNelson.Angular.Partial
open Wave Placement Set

/-- The two ends of an angular block give its rounded bounds on sine and
cosine, since both functions are monotone on the first quadrant. -/
private theorem rectangle {n i j : Nat} (hn : 0<n) (ij : i<j) (jn : j≤n) {θ : ℝ}
    (hθ : θ ∈ Icc (binEdge n i) (binEdge n j)) :
    let b := halfAngleBox n i j
    Real.cos θ ∈ Icc ((b.xlo:ℝ)/S) ((b.xhi:ℝ)/S) ∧
    Real.sin θ ∈ Icc ((b.ylo:ℝ)/S) ((b.yhi:ℝ)/S) ∧
    Real.cos θ ∈ Icc 0 1 ∧ Real.sin θ ∈ Icc 0 1 := by
  cases j with
  | zero => omega
  | succ j =>
    have first : i < n := by omega
    have last : j < n := by omega
    let bin := binEdge n
    have el := bin_component_bounds hn first ⟨le_rfl,binEdge_mono n i⟩
    have er := bin_component_bounds hn last ⟨binEdge_mono n j,le_rfl⟩
    obtain ⟨lx,ly⟩ := box_encloses_components hn first el.1 el.2
    obtain ⟨rx,ry⟩ := box_encloses_components hn last er.1 er.2
    have units : (CompleteWave.scale:ℝ)=S := by norm_num [CompleteWave.scale,S]
    rw [units] at lx ly rx ry
    have first0 : 0 ≤ bin i := mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr (by positivity))
    have lastπ : bin (j+1) ≤ Real.pi/2 := by
      have h : ((j+1:Nat):ℝ)/(n:ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hn)).2 (by exact_mod_cast jn)
      have hh := Real.arctan_mono h
      rw [Real.arctan_one] at hh
      dsimp [bin,binEdge]
      linarith
    have tpos : 0≤θ := first0.trans hθ.1
    have tπ : θ≤Real.pi/2 := hθ.2.trans lastπ
    have cosL := Real.cos_le_cos_of_nonneg_of_le_pi tpos (lastπ.trans (by linarith [Real.pi_pos])) hθ.2
    have cosR := Real.cos_le_cos_of_nonneg_of_le_pi first0 (tπ.trans (by linarith [Real.pi_pos])) hθ.1
    have sinL := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ bin i by linarith [Real.pi_pos]) tπ hθ.1
    have sinR := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ θ by linarith [Real.pi_pos]) lastπ hθ.2
    let b := halfAngleBox n i (j+1)
    have cx : Real.cos θ ∈ Icc ((b.xlo:ℝ)/S) ((b.xhi:ℝ)/S) := ⟨rx.1.trans cosL,cosR.trans lx.2⟩
    have sy : Real.sin θ ∈ Icc ((b.ylo:ℝ)/S) ((b.yhi:ℝ)/S) := ⟨ly.1.trans sinL,sinR.trans ry.2⟩
    have hu : Real.cos θ∈Icc 0 1 :=
      ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],tπ⟩,Real.cos_le_one _⟩
    have hv : Real.sin θ∈Icc 0 1 :=
      ⟨Real.sin_nonneg_of_mem_Icc ⟨tpos,by linarith [Real.pi_pos]⟩,Real.sin_le_one _⟩
    exact ⟨cx,sy,hu,hv⟩

private theorem rectangle_bound {W : Datum} (p : Profile W) (b : Box) {u v : ℝ}
    (cx : u∈Icc ((b.xlo:ℝ)/S) ((b.xhi:ℝ)/S)) (sy : v∈Icc ((b.ylo:ℝ)/S) ((b.yhi:ℝ)/S))
    (hu : u∈Icc 0 1) (hv : v∈Icc 0 1) (yl : 0≤b.ylo) :
    W.x*H*directionalMonoProb W (point u v) ≤ (area walls b:ℝ)/(2*S^2) := by
  have units : (CompleteWave.scale:ℝ)=S := by norm_num [CompleteWave.scale,S]
  apply (monoProb_box W hu hv cx sy (div_nonneg (by exact_mod_cast yl) (by norm_num [S]))).trans
  change _ ≤ (area walls b:ℝ)/(2*S^2)
  unfold area
  rw [Nat.cast_add,add_div]
  apply add_le_add (slice_bound p _ _ _ yl (sy.1.trans sy.2))
  have ref := reflected_enclosure sy.1 sy.2
  have ey : reflectedLow ((b.ylo:ℝ)/S) ((b.yhi:ℝ)/S) = (b.shiftY:ℝ)/S := by
    simpa only [reflectedLow,units] using shiftY_scaled b
  have ex : 2*W.x-(b.xhi:ℝ)/S = (shiftX b:ℝ)/S := by
    rw [p.x]
    norm_num [Partial.shiftX,PartialWave.xInt,S,sub_div]
  rw [ex,ey]
  apply slice_bound p _ _ _ (shiftY_nonneg _)
  simpa only [←ey] using ref.1.trans ref.2


/-- Every angular interval has its outward-rounded partial-wave overlap bound. -/
theorem cover {W : Datum} (p : Profile W) : Cover W := by
  intro i j ij jn θ hθ
  obtain ⟨cx,sy,hu,hv⟩ := rectangle (by decide : 0<bins) ij jn hθ
  exact rectangle_bound p (halfAngleBox bins i j) cx sy hu hv (ylo_nonneg ..)

end HadwigerNelson.Angular.Partial
