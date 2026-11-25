import HadwigerNelson.Certificate.Weighted

namespace HadwigerNelson.Certificate.ParameterBoxes

theorem disk_floor (k n : ℕ) :
    (⌊(((k:ℚ)/2:ℚ):ℝ)*(n:ℝ)⌋ : ℝ) = (k*n/2 : ℕ) := by
  have hx : (((k:ℚ)/2:ℚ):ℝ)*(n:ℝ) = ((k*n:ℕ):ℝ)/(2:ℕ) := by
    push_cast
    ring
  rw [hx,Int.floor_div_natCast,Int.floor_natCast,Int.ofNat_ediv_ofNat]
  rfl

private theorem seven_eq (f : ℕ → ℝ) : sumSeven f = ∑ i : Fin 7, f i.val := by
  simp [sumSeven, Fin.sum_univ_succ]
  ring

private theorem diskCount_eq (i : Fin 7) : diskCount i.val = Centres.diskLimit i := rfl

private theorem width_eq (i : Fin 7) : ((width i.val):ℝ) = Centres.excessWidth i := by
  simp [width,Centres.excessWidth,apply_ite]

private theorem firstTerms_eq (m s j : ℕ) (hs : s ≤ 10689) :
    firstTerms (m:ℝ) s j (variance (m:ℝ)) =
      (min ((10689:ℝ)*71152801254159 + m*708385488148)
        (min ((10689:ℝ)*71152801254159 + m*(708385488148-112668096940)
          - s*16034576942481 - j*3057937052494 +
          112668096940*Crossings.weightedBound 10689 m s j (828/1000) (1195/10000) +
          min ((10689-s:ℕ)*(150296106235:ℝ))
            (min ((10689-s:ℕ)*(97911102803:ℝ) + j*104770006866) (j*(300592212470:ℝ))))
         ((10689:ℝ)*71152801254159 + m*(708385488148-112668096940)
          - s*16034576942481 - j*3057937052494 +
          112668096940*Crossings.weightedBound 10689 m s j (828/1000) (6195/10000))))/10^18 := by
  unfold firstTerms
  simp only [real_const,weighted_eq,Nat.cast_sub hs]
  norm_num [order]
  ring

set_option maxHeartbeats 1800000 in
private theorem profile_eq (m s j : ℕ) (hsj : s+j ≤ 10689) (hi lo sl : ℚ) :
    credit (budgets (m:ℝ) s j (s+j:ℕ) (variance (m:ℝ))) hi lo sl =
    Centres.profileCredit 10689 m s j hi lo sl := by
  have rest : (order:ℝ) - (s+j:ℕ) = ((10689-(s+j):ℕ):ℝ) := by
    rw [Nat.cast_sub hsj]
    norm_num [order]
  unfold credit budgets Centres.profileCredit
  simp only [real_const,real_floor,weighted_eq,pairLower_eq,chooseTwo_eq,rest,seven_eq]
  simp only [disk_floor,diskCount_eq,width_eq]
  push_cast
  norm_num [order]
  congr 1 <;> ring_nf <;> simp only [Nat.mul_comm]

theorem objective_eq (m s j : ℕ) (hsj : s+j ≤ 10689) :
    objective (m:ℝ) s j (s+j:ℕ) = pointObjective 10689 m s j := by
  unfold objective pointObjective Centres.centreCredit
  dsimp only
  rw [firstTerms_eq m s j (by omega),profile_eq _ _ _ hsj,profile_eq _ _ _ hsj]
  norm_num

end HadwigerNelson.Certificate.ParameterBoxes
