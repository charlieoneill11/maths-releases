import HadwigerNelson.Centres.Events.Definitions
import HadwigerNelson.Wave.Geometry.Blank

/-! Width comparisons and uniqueness of the hole translate in the small
central window used for a unit tail. -/

namespace HadwigerNelson.Centres
open Set Wave
noncomputable section

theorem width_nonneg (W : Datum) (y : ℝ) : 0≤width W y := by
  unfold width; split <;> first | exact le_rfl | exact (W.left_bounds _).1

theorem width_lt (W : Datum) (y : ℝ) : width W y<1/5 := by
  unfold width; split
  · exact (W.left_bounds _).2
  · norm_num

theorem width_antitone (W : Datum) {a b : ℝ} (hab : |a|≤|b|) : width W b ≤ width W a := by
  by_cases hi : |b|≤W.y0
  · rw [width,if_pos hi,width,if_pos (hab.trans hi)]
    have bound : W.y0 ≤ H/2 := by linarith [W.y0_bounds.2,H_pos]
    exact W.left_antitone ⟨abs_nonneg _,hab.trans (hi.trans bound)⟩ ⟨abs_nonneg _,hi.trans bound⟩ hab
  · rw [width,if_neg hi]; exact width_nonneg W _

private theorem abs_left (W : Datum) (y : ℝ) : W.left |y|=W.left y := by
  rcases le_or_gt 0 y with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h,W.left_even]

theorem in_hole_of_width (W : Datum) {z : Plane} {s : ℝ} (x : |z 0|<width W s) (y : |z 1|≤s) :
    z∈hole W := by
  have h := x.trans_le (width_antitone W (a:=z 1) (b:=s) (y.trans (le_abs_self _)))
  by_cases hs : |z 1|≤W.y0
  · exact ⟨hs,by simpa only [width,if_pos hs,abs_left] using h.le⟩
  · rw [width,if_neg hs] at h
    exact False.elim ((abs_nonneg _).not_gt h)

theorem hole_width (W : Datum) {z : Plane} (h : z∈hole W) : |z 0|≤width W (z 1) := by
  rw [width,if_pos h.1,abs_left]; exact h.2

theorem copy_blank (W : Datum) (i j : ℤ) {z : Plane} (h : z-holeLatticePoint W i j∈hole W) :
    Wave.colour W z=none := holeCopies_subset_blank W ⟨i,j,h⟩

theorem shifted_copy_blank (W : Datum) (i j h : ℤ) {z : Plane}
    (mem : z-holeLatticePoint W i j-Wave.point 0 (h:ℝ)∈hole W) : Wave.colour W z=none := by
  apply copy_blank W i (j+2*h)
  have eq : z-holeLatticePoint W i (j+2*h) = z-holeLatticePoint W i j-Wave.point 0 (h:ℝ) := by
    ext k; fin_cases k <;> simp [holeLatticePoint,H] <;> ring
  rwa [eq]

/-- A translate with a point within the central half-width and quarter-height
window has exactly the same lattice index as that window. -/
theorem central_hole (W : Datum) (i j : ℤ) {z : Plane} (mem : z∈holeCopies W)
    (x : |(z-holeLatticePoint W i j) 0|≤1/2) (y : |(z-holeLatticePoint W i j) 1|≤1/4) :
    z-holeLatticePoint W i j∈hole W := by
  obtain ⟨k,l,h⟩ := mem
  have hx := h.2.trans_lt (W.left_bounds _).2
  have hy := h.1.trans_lt W.y0_bounds.2
  change |z 0-2*W.x*k|<1/5 at hx
  change |z 0-2*W.x*i|≤1/2 at x
  obtain ⟨xl,xr⟩ := abs_le.mp x
  obtain ⟨hl,hr⟩ := abs_lt.mp hx
  have step : 0≤2*W.x := by linarith [W.x_bounds.1]
  have eq : k=i := by
    rcases lt_trichotomy k i with a|a|a
    · have gap : (k:ℝ)+1 ≤ i := by exact_mod_cast (show k + 1 ≤ i by omega)
      nlinarith [mul_le_mul_of_nonneg_left gap step,W.x_bounds.1]
    · exact a
    · have gap : (i:ℝ)+1 ≤ k := by exact_mod_cast (show i + 1 ≤ k by omega)
      nlinarith [mul_le_mul_of_nonneg_left gap step,W.x_bounds.1]
  subst k
  change |z 1-((3/2)*H*i+H*l)|<H/4 at hy
  change |z 1-((3/2)*H*i+H*j)|≤1/4 at y
  have eq' : l=j := by
    obtain ⟨yl,yr⟩ := abs_le.mp y
    obtain ⟨hyl,hyr⟩ := abs_lt.mp hy
    rcases lt_trichotomy l j with a|a|a
    · have gap : (l:ℝ)+1 ≤ j := by exact_mod_cast (show l + 1 ≤ j by omega)
      norm_num [H] at *; linarith
    · exact a
    · have gap : (j:ℝ)+1 ≤ l := by exact_mod_cast (show j + 1 ≤ l by omega)
      norm_num [H] at *; linarith
  simpa only [eq'] using h

end
end HadwigerNelson.Centres
