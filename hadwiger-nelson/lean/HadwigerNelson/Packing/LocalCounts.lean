import HadwigerNelson.Packing.Radial
import HadwigerNelson.Packing.Disks

namespace HadwigerNelson.Packing

/-- Six points in a closed disc of radius d contain two at distance at most d. -/
theorem five_neighbours (P : Finset Plane) (z : Plane) {d : ℝ} (hd : 0 < d)
    (sep : separated P d) (inside : ∀ x ∈ P, dist x z ≤ d) : P.card ≤ 5 := by
  apply radial_card P z (l:=0) (u:=1) (C:=1/2) hd sep (by decide)
  · intro x hx
    exact ⟨div_nonneg dist_nonneg hd.le,(div_le_one hd).mpr (inside x hx)⟩
  · norm_num only [Nat.cast_ofNat]
    rw [show 2*Real.pi/6 = Real.pi/3 by ring,Real.cos_pi_div_three]
  · intro a ha b hb
    apply radial_corners ha hb <;> norm_num

theorem fourteen_neighbours (P : Finset Plane) (z : Plane) (sep : separated P (53/10000))
    (inside : ∀ x ∈ P, dist x z ≤ 1837/250000) : P.card ≤ 14 := by
  have bound := disks P z (ρ:=(53/10000)/2) (by norm_num) (by norm_num)
    (by convert sep using 1 <;> norm_num) inside
  have lt : (P.card:ℝ) < 15 := bound.trans_lt (by norm_num)
  exact Nat.le_of_lt_succ (by exact_mod_cast lt)

/-- The thin annulus around a member of R contains at most eight other members of R. -/
theorem eight_neighbours (P : Finset Plane) (z : Plane) (sep : separated P (53/10000))
    (radii : ∀ x ∈ P, 53/10000 ≤ dist x z ∧ dist x z ≤ 1837/250000) : P.card ≤ 8 := by
  let u : ℝ := (1837/250000)/(53/10000)
  let C : ℝ := 1-(2*(355/113)/9)^2/2
  apply radial_card P z (l:=1) (u:=u) (C:=C) (by norm_num) sep (by decide)
  · intro x hx
    exact ⟨(one_le_div (by norm_num)).mpr (radii x hx).1,
      div_le_div_of_nonneg_right (radii x hx).2 (by norm_num)⟩
  · norm_num only [Nat.cast_ofNat,show (8:ℝ)+1=9 by norm_num]
    have pi : Real.pi ≤ 355/113 := by linarith [Real.pi_lt_d20]
    have hs : (2*Real.pi/9)^2 ≤ (2*(355/113)/9)^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith [Real.one_sub_sq_div_two_le_cos (x:=2*Real.pi/9)]
  · intro a ha b hb
    apply radial_corners ha hb <;> norm_num [u,C]

end HadwigerNelson.Packing
