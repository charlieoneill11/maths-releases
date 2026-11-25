import HadwigerNelson.Stars.LocalGain
import HadwigerNelson.Placement.Coordinates
import HadwigerNelson.Wave.Geometry.Halves

namespace HadwigerNelson.Stars
noncomputable section

def direction (t : ℝ) := Wave.point (Real.cos t) (Real.sin t)

def angleScore {d : Nat} (W : Wave.Datum) (φ : Fin d → ℝ) (z : Plane) (θ : ℝ) : ℝ :=
  localGain (Wave.colour W z) (fun j => Wave.colour W (z + direction (θ+φ j)))

theorem angleScore_period {d : Nat} (W : Wave.Datum) (φ : Fin d → ℝ) (z : Plane) :
    Function.Periodic (angleScore W φ z) (2*Real.pi) := by
  intro θ
  unfold angleScore
  congr 1
  funext j
  simp only [direction,add_right_comm θ (2*Real.pi) (φ j),Real.cos_add_two_pi,Real.sin_add_two_pi]

def copyMap (b h : Bool) (k : Fin 3) (z : Plane) :=
  Wave.halfImage b k (if h then Wave.sigma1 z else z)

def copyPerm (b h : Bool) (k : Fin 3) : Equiv.Perm Wave.Label :=
  ((if h then Wave.sigma1Perm else Equiv.refl _).trans
    (if b then Wave.sigma2Perm else Equiv.refl _)).trans (Wave.tauPerm k.val)

theorem colour_copy (W : Wave.Datum) (b h : Bool) (k : Fin 3) (z : Plane) :
    Wave.colour W (copyMap b h k z) = (Wave.colour W z).map (copyPerm b h k) := by
  cases b <;> cases h <;>
    simp [copyMap,copyPerm,Wave.halfImage,Wave.colour_tau,Wave.colour_sigma1,Wave.colour_sigma2,
      Option.map_map,Wave.tauPerm,Wave.sigma1Perm,Wave.sigma2Perm]

def signAngle (b h : Bool) (t : ℝ) : ℝ := if b=h then t else -t

def turnAngle (b h : Bool) (t : ℝ) : ℝ := (if b then Real.pi else 0) + signAngle b h t

/-- An affine symmetry sends the inverse-transformed direction back to the
original one. The effect on the centre is kept separate from the direction. -/
theorem copy_direction (b h : Bool) (k : Fin 3) (z : Plane) (t : ℝ) :
    copyMap b h k (z+direction (turnAngle b h t)) = copyMap b h k z + direction t := by
  ext i
  fin_cases i <;> cases b <;> cases h <;>
    simp [copyMap,Wave.halfImage,Wave.sigma1,Wave.sigma2,Wave.tau,direction,turnAngle,signAngle,
      Real.sin_add,Real.cos_add] <;> ring

private theorem turn_add (b h : Bool) (x y : ℝ) :
    turnAngle b h (x+y) = turnAngle b h x + signAngle b h y := by
  cases b <;> cases h <;> simp [turnAngle,signAngle] <;> ring

theorem angleScore_copy {d : Nat} (W : Wave.Datum) (φ : Fin d → ℝ)
    (z : Plane) (b h : Bool) (k : Fin 3) (θ : ℝ) :
    angleScore W φ (copyMap b h k z) θ =
      angleScore W (fun j => signAngle b h (φ j)) z (turnAngle b h θ) := by
  unfold angleScore
  simp_rw [← copy_direction,colour_copy,turn_add]
  exact localGain_relabel _ _ _

end
end HadwigerNelson.Stars
