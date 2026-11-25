import HadwigerNelson.Wave.Geometry.Partial
import HadwigerNelson.Placement.Height
import HadwigerNelson.Arithmetic.Rounding

/-! Physical interpolation for the complete strip interval and the active
part of the lower wall in the partial-wave angular calculation. -/

namespace HadwigerNelson.Angular.Partial
open Set
noncomputable section

structure Profile (W : Wave.Datum) : Prop where
  x : W.x = 923111560246/10^12
  left : ∀ i : Fin 17, ∀ u ∈ Icc (0:ℝ) 1, W.left (((i:ℝ)+u)*54/100000) =
    ((1-u)*(PartialWave.leftKnots[i.val]!.2:ℝ)+u*(PartialWave.leftKnots[i.val+1]!.2:ℝ))/10^12
  right : ∀ i : Fin 512, ∀ u ∈ Icc (0:ℝ) 1, W.right (((i:ℝ)+u)*Wave.H/512) =
    ((1-u)*(PartialWave.rightKnots[i.val]!.2:ℝ)+u*(PartialWave.rightKnots[i.val+1]!.2:ℝ))/10^12

theorem datum_profile : Profile PartialWave.datum :=
  ⟨PartialWave.datum_x, PartialWave.datum_left_segment, PartialWave.datum_right_segment⟩

def scaledRight (q : ℕ) (z : ℝ) : ℝ :=
  Arithmetic.linearAt ((q:ℝ)*976562500) (PartialWave.rightKnot q).2
    (((q:ℝ)+1)*976562500) (PartialWave.rightKnot (q+1)).2 z

def scaledLeft (l : ℕ) (z : ℝ) : ℝ :=
  Arithmetic.linearAt ((l:ℝ)*540000000) (PartialWave.leftKnot l).2
    (((l:ℝ)+1)*540000000) (PartialWave.leftKnot (l+1)).2 z

private theorem left_bang (i : ℕ) (hi : i < 37) : PartialWave.leftKnots[i]! = PartialWave.leftKnot i := by
  rw [getElem!_pos _ _ (by simpa [PartialWave.leftKnots] using hi), PartialWave.get_leftKnots _ hi]

private theorem right_bang (i : ℕ) (hi : i < 513) : PartialWave.rightKnots[i]! = PartialWave.rightKnot i := by
  rw [getElem!_pos _ _ (by simpa [PartialWave.rightKnots] using hi), PartialWave.get_rightKnots _ hi]

private theorem barycentric_eq (q t z v w : ℝ) (ht : t ≠ 0) :
    (1-(z/t-q))*v+(z/t-q)*w = Arithmetic.linearAt (q*t) v ((q+1)*t) w z := by
  rw [Arithmetic.linearAt, show (q+1)*t-q*t=t by ring]
  field_simp
  ring

theorem Profile.right_cell {W : Wave.Datum} (p : Profile W) (q : ℕ) (hq : q<512)
    {z : ℝ} (hz : z ∈ Icc ((q:ℝ)*976562500) (((q:ℝ)+1)*976562500)) :
    (10^12:ℝ)*W.right (z/10^12) = scaledRight q z := by
  let u := z/976562500-(q:ℝ)
  have hu : u ∈ Icc (0:ℝ) 1 := by
    obtain ⟨lo,hi⟩ := hz
    dsimp [u]
    constructor <;> linarith
  have h := p.right ⟨q,hq⟩ u hu
  change W.right (((q:ℝ)+u)*Wave.H/512) = _ at h
  rw [show ((q:ℝ)+u)*Wave.H/512=z/10^12 by dsimp [u,Wave.H]; ring,
    right_bang _ (by omega), right_bang _ (by omega)] at h
  rw [h, mul_div_cancel₀ _ (by norm_num : (10:ℝ)^12 ≠ 0)]
  exact barycentric_eq _ _ _ _ _ (by norm_num)

theorem Profile.left_cell {W : Wave.Datum} (p : Profile W) (l : ℕ) (hl : l<17)
    {z : ℝ} (hz : z ∈ Icc ((l:ℝ)*540000000) (((l:ℝ)+1)*540000000)) :
    (10^12:ℝ)*W.left (z/10^12) = scaledLeft l z := by
  let u := z/540000000-(l:ℝ)
  have hu : u ∈ Icc (0:ℝ) 1 := by
    obtain ⟨lo,hi⟩ := hz
    dsimp [u]
    constructor <;> linarith
  have h := p.left ⟨l,hl⟩ u hu
  change W.left (((l:ℝ)+u)*54/100000) = _ at h
  rw [show ((l:ℝ)+u)*54/100000=z/10^12 by dsimp [u]; ring,
    left_bang _ (by omega), left_bang _ (by omega)] at h
  rw [h, mul_div_cancel₀ _ (by norm_num : (10:ℝ)^12 ≠ 0)]
  exact barycentric_eq _ _ _ _ _ (by norm_num)

/-- On the active lower wall, the closest admissible height is the lower
endpoint displacement. The entire 17-cell support fits below H/2. -/
theorem closestHeight_left (W : Wave.Datum) {lo hi y : ℝ} (hspan : lo ≤ hi)
    (active : y-lo ≤ 17*540000000/(10:ℝ)^12) :
    W.left (Placement.closestHeight Wave.H lo hi y) = W.left (y-lo) := by
  have h : y-lo ≤ Wave.H/2 := active.trans (by norm_num [Wave.H])
  rw [Placement.closestHeight, min_eq_right h, max_eq_right (by linarith)]

end
end HadwigerNelson.Angular.Partial
