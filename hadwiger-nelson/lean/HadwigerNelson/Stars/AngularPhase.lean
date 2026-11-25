import HadwigerNelson.Stars.PhaseMoments
import HadwigerNelson.Stars.Envelope
import HadwigerNelson.Stars.RealFourier.Character
import HadwigerNelson.Arithmetic.Phase

/-! Half-angle coordinates and signed quadrant rotations used by both the
physical rectangle classifier and the finite Fourier endpoint powers. -/

namespace HadwigerNelson.Stars.BoxCheck
open Arithmetic Set

noncomputable def paramAngle (q : Nat) (t : ℝ) : ℝ := 2*Real.arctan t+q*(Real.pi/2)

noncomputable def endpoint (q i : Nat) : ℝ := paramAngle q ((i : ℝ)/resolution)

theorem paramAngle_succ (q : Nat) (t : ℝ) :
    paramAngle (q+1) t = paramAngle q t+Real.pi/2 := by unfold paramAngle; push_cast; ring

private theorem params (q : Nat) (hq : q < 4) (t : ℝ) :
    (Real.cos (paramAngle q t), Real.sin (paramAngle q t)) =
    match q with
    | 0 => (rayX t,rayY t)
    | 1 => (-rayY t,rayX t)
    | 2 => (-rayX t,-rayY t)
    | _ => (rayY t,-rayX t) := by
  have b : paramAngle 0 t = 2*Real.arctan t := by simp [paramAngle]
  have e1 := paramAngle_succ 0 t
  have e2 := paramAngle_succ 1 t
  have e3 := paramAngle_succ 2 t
  change paramAngle 1 t = _ at e1
  change paramAngle 2 t = _ at e2
  change paramAngle 3 t = _ at e3
  interval_cases q <;> simp only [e3,e2,e1,b,cos_two_arctan,sin_two_arctan,
    Real.cos_add_pi_div_two,Real.sin_add_pi_div_two,neg_neg]

theorem endpoint_phase (q i : Nat) (hq : q < 4) : anglePhase (endpoint q i) = exactPhase q i := by
  have θ : endpoint q i = (q : ℝ)*Real.pi/2+2*Real.arctan ((i : ℝ)/resolution) := by
    unfold endpoint paramAngle; ring
  rw [anglePhase,θ]
  have e := phase_integer_point (resolution : Int) (i : Int) q (by decide)
  simp only [Int.cast_natCast] at e
  rw [e]
  interval_cases q <;> rfl

theorem endpoint_monotone (q : Nat) : Monotone (endpoint q) := by
  intro a b hab
  dsimp [endpoint,paramAngle]
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.arctan_mono (div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity))

theorem endpoint_edge (q : Nat) :
    endpoint q resolution = endpoint (q+1) 0 := by
  simp [endpoint,paramAngle,Real.arctan_one,
    show (resolution : ℝ) ≠ 0 by norm_num [resolution]]
  ring

theorem endpoint_zero : endpoint 0 0 = 0 := by simp [endpoint,paramAngle]
theorem endpoint_full : endpoint 3 resolution = 2*Real.pi := by
  rw [endpoint_edge]
  simp [endpoint,paramAngle]
  ring

/-- Every point of the real angular interval has a parameter in its exact
rational slice, including both endpoints. -/
theorem angle_parameter (q a b : Nat) (hab : a ≤ b) {θ : ℝ}
    (hθ : θ ∈ Icc (endpoint q a) (endpoint q b)) :
    ∃ t ∈ Icc ((a : ℝ)/resolution) ((b : ℝ)/resolution), paramAngle q t = θ := by
  exact intermediate_value_Icc (div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity))
    ((continuous_const.mul Real.continuous_arctan).add continuous_const).continuousOn hθ

theorem quarter_contains (a b : Nat) {t : ℝ} (hb : b ≤ resolution)
    (ht : t ∈ Icc ((a : ℝ)/resolution) ((b : ℝ)/resolution)) :
    ClosedBox (Angular.halfAngleBox resolution a b) (CompleteWave.scale*rayX t)
      (CompleteWave.scale*rayY t) := by
  have h := ray_bin_bounds (S := (CompleteWave.scale : Int)) (N := (resolution : Int))
    (i := a) (j := b) (t := t) (by decide) (by decide) (by positivity)
    (by exact_mod_cast hb) (by simpa using ht.1) (by simpa using ht.2)
  simpa [ClosedBox,Angular.halfAngleBox,rayXNum,rayYNum,rayDen] using h

theorem ray_contains {q a b : Nat} (hq : q < 4) (hab : a ≤ b) (hb : b ≤ resolution) {θ : ℝ}
    (hθ : θ ∈ Icc (endpoint q a) (endpoint q b)) :
    ClosedBox (quadrant q (Angular.halfAngleBox resolution a b))
      (CompleteWave.scale*Real.cos θ) (CompleteWave.scale*Real.sin θ) := by
  obtain ⟨t,ht,rfl⟩ := angle_parameter q a b hab hθ
  have p := params q hq t
  rcases quarter_contains a b hb ht with ⟨x0,x1,y0,y1⟩
  have hx := congrArg Prod.fst p
  have hy := congrArg Prod.snd p
  interval_cases q <;> simp [quadrant,ClosedBox] at hx hy ⊢ <;>
    simp only [hx,hy,mul_neg] <;> constructor <;> repeat first | assumption | constructor | linarith

end HadwigerNelson.Stars.BoxCheck
