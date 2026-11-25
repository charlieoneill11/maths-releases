import Chowla.Statement
import Mathlib.Data.Nat.Squarefree

namespace Chowla

private theorem primeFactors_neg_four : (Int.natAbs (-4)).primeFactors.erase 2 = ∅ := by decide +kernel

private theorem primeFactors_eight : (Int.natAbs 8).primeFactors.erase 2 = ∅ := by decide +kernel

theorem chi_neg_four : chi (-4) = ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) := by
  unfold chi
  rw [primeFactors_neg_four]
  have h8 : ¬ 8 ∣ (Int.natAbs (-4)) := by decide +kernel
  have h4 : 4 ∣ Int.natAbs (-4) := by decide +kernel
  simpa only [Finset.prod_empty, mul_one, dyadicCharacter, dif_neg h8, dif_pos h4] using
    (DirichletCharacter.changeLevel_self (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)))

theorem chi_eight : chi 8 = ZMod.χ₈.ringHomComp (Int.castRingHom ℂ) := by
  unfold chi
  rw [primeFactors_eight]
  have h8 : 8 ∣ (Int.natAbs 8) := by decide +kernel
  have h : ((8 : ℤ) / 8) % 4 = 1 := by decide +kernel
  simpa only [Finset.prod_empty, mul_one, dyadicCharacter, dif_pos h8, if_pos h] using
    (DirichletCharacter.changeLevel_self (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)))

theorem isFundDisc_neg_four : IsFundDisc (-4) := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

theorem isFundDisc_five : IsFundDisc 5 := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

theorem isFundDisc_eight : IsFundDisc 8 := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

theorem isFundDisc_neg_eight : IsFundDisc (-8) := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

theorem isFundDisc_twelve : IsFundDisc 12 := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

theorem not_isFundDisc_four : ¬ IsFundDisc 4 := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

theorem not_isFundDisc_nine : ¬ IsFundDisc 9 := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

theorem not_isFundDisc_sixteen : ¬ IsFundDisc 16 := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

theorem not_isFundDisc_neg_sixteen : ¬ IsFundDisc (-16) := by
  unfold IsFundDisc
  simp only [← Int.squarefree_natAbs]
  decide +kernel

end Chowla
