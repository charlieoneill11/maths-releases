import HadwigerNelson.Angular.Boxes

namespace HadwigerNelson.Angular
open Arithmetic Set

private theorem encloses_ray {n i j : Nat} {t : ℝ} (hn : 0 < n) (hj : j ≤ n)
    (hi : (i:ℝ)/n ≤ t) (ht : t ≤ (j:ℝ)/n) :
    let b := halfAngleBox n i j
    rayX t ∈ Icc (b.xlo / (CompleteWave.scale:ℝ)) (b.xhi/(CompleteWave.scale:ℝ)) ∧
    rayY t ∈ Icc (b.ylo / (CompleteWave.scale:ℝ)) (b.yhi/(CompleteWave.scale:ℝ)) := by
  let S : Int := CompleteWave.scale
  have e := ray_bin_bounds (S := S) (N := (n:Int)) (i := (i:Int)) (j := (j:Int)) (t := t)
    (by dsimp [S]; positivity) (by exact_mod_cast hn) (by positivity)
    (by exact_mod_cast hj) (by simpa using hi) (by simpa using ht)
  let b := halfAngleBox n i j
  change (b.xlo:ℝ) ≤ (S:ℝ)*rayX t ∧ (S:ℝ)*rayX t ≤ b.xhi ∧
    (b.ylo:ℝ) ≤ (S:ℝ)*rayY t ∧ (S:ℝ)*rayY t ≤ b.yhi at e
  have pos : (0:ℝ) < (S:ℝ) := by norm_num [S,CompleteWave.scale]
  rcases e with ⟨xl,xh,yl,yh⟩
  refine ⟨⟨(div_le_iff₀ pos).2 ?_,(le_div_iff₀ pos).2 ?_⟩,
    ⟨(div_le_iff₀ pos).2 ?_,(le_div_iff₀ pos).2 ?_⟩⟩
  all_goals first | simpa [mul_comm] using xl | simpa [mul_comm] using xh |
    simpa [mul_comm] using yl | simpa [mul_comm] using yh

theorem box_encloses_components {n j : Nat} {u v : ℝ} (hn : 0<n) (hj : j<n)
    (hu : u ∈ Icc (rayX (((j:ℝ)+1)/n)) (rayX ((j:ℝ)/n)))
    (hv : v ∈ Icc (rayY ((j:ℝ)/n)) (rayY (((j:ℝ)+1)/n))) :
    let b := halfAngleBox n j (j+1)
    u ∈ Icc (b.xlo/(CompleteWave.scale:ℝ)) (b.xhi/(CompleteWave.scale:ℝ)) ∧
    v ∈ Icc (b.ylo/(CompleteWave.scale:ℝ)) (b.yhi/(CompleteWave.scale:ℝ)) := by
  have inj : (j:ℝ)/n ≤ ((j+1:Nat):ℝ)/n :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) (by positivity)
  have low := encloses_ray hn (Nat.succ_le_of_lt hj) (i := j) le_rfl inj
  have high := encloses_ray hn (Nat.succ_le_of_lt hj) (i := j) inj le_rfl
  simp only [Nat.cast_add,Nat.cast_one] at high
  exact ⟨⟨high.1.1.trans hu.1,hu.2.trans low.1.2⟩,
    ⟨low.2.1.trans hv.1,hv.2.trans high.2.2⟩⟩

theorem ylo_nonneg (n i j : Nat) : 0 ≤ (halfAngleBox n i j).ylo := by
  unfold halfAngleBox
  exact Int.ediv_nonneg (by positivity) (by positivity)

theorem shiftY_nonneg (b : Box) : 0 ≤ b.shiftY := le_max_left _ _

theorem shiftY_scaled (b : Box) :
    max 0 (max (3/4 - b.yhi/(CompleteWave.scale:ℝ)) (b.ylo/(CompleteWave.scale:ℝ) - 3/4)) =
    (b.shiftY:ℝ)/(CompleteWave.scale:ℝ) := by
  let s : ℝ := CompleteWave.scale
  have hs : 0 ≤ s := by norm_num [s,CompleteWave.scale]
  have q : (3/4:ℝ) = 750000000000/s := by norm_num [s,CompleteWave.scale]
  change max 0 (max (3/4-(b.yhi:ℝ)/s) ((b.ylo:ℝ)/s-3/4)) = (b.shiftY:ℝ)/s
  rw [q,←sub_div,←sub_div,max_div_div_right hs]
  rw [show (0:ℝ) = 0/s by simp,max_div_div_right hs]
  simp [Box.shiftY]

theorem shiftX_scaled (b : Box) :
    2*((CompleteWave.xInt:ℝ)/CompleteWave.scale) - b.xhi/(CompleteWave.scale:ℝ) =
    (b.shiftX:ℝ)/(CompleteWave.scale:ℝ) := by
  simp [Box.shiftX,sub_div,mul_div_assoc]

end HadwigerNelson.Angular
