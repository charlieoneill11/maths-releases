import HadwigerNelson.Data.PartialWave
import HadwigerNelson.Angular.GridRational
import HadwigerNelson.Wave.Geometry.GridBounds

namespace HadwigerNelson.PartialWave
open Wave Angular.Grid
noncomputable section

def xq : ℚ := 923111560246 / 1000000000000
def cutoff : ℝ := 9180000000 / 1000000000000

def rightOrd (i : Nat) : ℚ := ((rightKnot i).2 : ℚ)/1000000000000

def rightAt (y : ℝ) : ℝ := interpolation (fun i => (rightOrd i : ℝ)) 512 (1024*y)

private theorem cast_right (i : Nat) : (rightOrd i : ℝ) = ((rightKnot i).2 : ℝ)/1000000000000 := by
  simp [rightOrd]

private theorem arg_mem {y : ℝ} (hy : y∈Set.Icc 0 H) : 1024*y ∈ Set.Icc 0 (512:ℝ) := by
  obtain ⟨lo,hi⟩ := hy
  unfold H at hi
  constructor <;> linarith

theorem rightAt_continuous : Continuous rightAt :=
  (interpolation_continuous _ _).comp (continuous_const.mul continuous_id)

theorem rightAt_rational : RationalProfile rightAt := by
  simpa only [rightAt,show (2:ℝ)*(512:Nat)=1024 by norm_num] using rationalProfile rightOrd 512 (by decide)

theorem rightAt_reflect (y : ℝ) (hy : y∈Set.Icc 0 H) : rightAt (H-y) = rightAt y := by
  unfold rightAt
  rw [show 1024*(H-y)=512-1024*y by unfold H; ring]
  apply reflect _ _ (by decide) _ (arg_mem hy)
  intro i hi
  rw [cast_right,cast_right,(right_knot_ok i hi).2.1]

theorem rightAt_complement (y : ℝ) (hy : y∈Set.Icc 0 (H/2)) : rightAt y+rightAt (y+H/2)=2*(xq:ℝ) := by
  unfold rightAt
  rw [show 1024*(y+H/2)=1024*y+256 by unfold H; ring]
  apply complement _ 256 _ (by decide)
  · intro i hi
    have h := (right_knot_ok i (by omega)).2.2.1.2.2.2 hi
    change (rightKnot i).2+(rightKnot (i+256)).2=2*923111560246 at h
    have h' : ((rightKnot i).2:ℝ)+(rightKnot (i+256)).2=2*923111560246 := by exact_mod_cast h
    rw [cast_right,cast_right]
    norm_num [xq]
    linarith
  · obtain ⟨lo,hi⟩ := hy
    unfold H at hi
    change 0 ≤ 1024*y ∧ 1024*y ≤ (256:ℝ)
    constructor <;> linarith

theorem rightAt_bounds (y : ℝ) (hy : y∈Set.Icc 0 H) : 4/5<rightAt y ∧ rightAt y<1 := by
  apply between _ (by decide) _ (arg_mem hy)
  intro i hi
  have h := (right_knot_ok i hi).2.2.1
  have lo : 4*1000000000000 < 5*((rightKnot i).2:ℝ) := by exact_mod_cast h.2.1
  have up : ((rightKnot i).2:ℝ) < 1000000000000 := by exact_mod_cast h.2.2.1
  rw [cast_right]
  constructor <;> linarith

theorem rightAt_lipschitz (y z : ℝ) (hy : y∈Set.Icc 0 H) (hz : z∈Set.Icc 0 H) :
    |rightAt y-rightAt z| ≤ |y-z| := by
  have slope (i : Nat) (hi : i<512) : |(rightOrd (i+1):ℝ)-(rightOrd i:ℝ)|≤1/1024 := by
    have a := right_knot_ok i hi.le
    have b := right_knot_ok (i+1) (by omega)
    obtain ⟨_,lo,up,_⟩ := a.2.2.2 hi
    rw [a.2.2.1.1,b.2.2.1.1] at lo up
    have l : ((rightKnot (i+1)).2:ℝ)+i*976562500 ≤ (rightKnot i).2+((i:ℝ)+1)*976562500 := by exact_mod_cast lo
    have u : ((rightKnot i).2:ℝ)+i*976562500 ≤ (rightKnot (i+1)).2+((i:ℝ)+1)*976562500 := by exact_mod_cast up
    rw [cast_right,cast_right,abs_le]
    constructor <;> linarith
  have h := interpolation_lipschitz (fun i => (rightOrd i:ℝ)) 512 (by decide) (1/1024) slope (arg_mem hy) (arg_mem hz)
  rw [← mul_sub,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1024)] at h
  unfold rightAt
  linarith

theorem rightAt_mono : MonotoneOn rightAt (Set.Icc 0 (H/2)) := by
  let v := fun i => (rightOrd i:ℝ)
  have mono := interpolation_mono v 256 (fun i hi => by
    have ki := right_knot_ok i (by omega)
    have h := (ki.2.2.2 (by omega)).2.2.2
    have low : (rightKnot i).1 < scale/4 := by rw [ki.2.2.1.1]; unfold scale; omega
    dsimp [v]; rw [cast_right,cast_right]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h low) (by norm_num))
  have eq (z : ℝ) (hz : z∈Set.Icc 0 (H/2)) : rightAt z=interpolation v 256 (1024*z) := by
    have lo := hz.1; have up := hz.2; unfold H at up
    obtain ⟨i,hi,it⟩ := hasCell (n:=256) (by decide) (show 1024*z∈Set.Icc 0 (256:ℝ) from ⟨by linarith,by linarith⟩)
    unfold rightAt
    exact (interpolation_on _ (show i<512 by omega) it).trans (interpolation_on v hi it).symm
  intro y hy z hz le
  rw [eq y hy,eq z hz]
  exact mono (by linarith)
end
end HadwigerNelson.PartialWave
