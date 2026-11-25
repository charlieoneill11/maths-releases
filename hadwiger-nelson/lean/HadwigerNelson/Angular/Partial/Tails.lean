import HadwigerNelson.Angular.Tails
import HadwigerNelson.Angular.Partial.Runtime

namespace HadwigerNelson.Angular.Partial

set_option maxRecDepth 16000 in
private theorem ordinate_upper : ∀ i : Fin 513, (PartialWave.rightKnot i).2 ≤ 971500000000 := by
  decide +kernel

private theorem extrema : walls.tree.stats.stop = (500000000000:Int) ∧
    walls.tree.stats.high ≤ (971500000000:Int) := by
  apply tree_extrema
  intro i _ hi
  have h : i < 513 := by omega
  simp only [rightValues,PartialWave.rightKnots,Array.getElem?_map,Array.getElem?_range,h,
    ↓reduceIte,Option.map_some,Option.getD_some]
  exact_mod_cast ordinate_upper ⟨i,h⟩

private theorem empty_slice {d lo : Int}
    (h : walls.tree.stats.stop ≤ lo ∨ walls.tree.stats.high ≤ d) : slice walls d lo=0 := by
  have z := misses_of_extreme _ d lo h
  simp only [slice,z,Bool.true_or,ite_true]

private theorem low {i j : Nat} (ij : i≤j) (le : j≤3*groupSize) :
    area walls (halfAngleBox bins i j)=0 := by
  obtain ⟨xl,_xh,yl,yh⟩ := halfAngleBox_refines (by decide : 0<bins) (Nat.zero_le i)
    ij le (by decide : 3*groupSize≤bins)
  have sy : (halfAngleBox bins 0 (3*groupSize)).shiftY ≤ (halfAngleBox bins i j).shiftY :=
    max_le_max_left 0 (max_le_max (sub_le_sub_left yh _) (sub_le_sub_right yl _))
  have h1 := empty_slice (lo:=(halfAngleBox bins i j).ylo)
    (.inr (extrema.2.trans ((by decide : (971500000000:Int) ≤ (halfAngleBox bins 0 (3*groupSize)).xlo).trans xl)))
  have h2 := empty_slice (d:=shiftX (halfAngleBox bins i j))
    (.inl (extrema.1.le.trans ((by decide : (500000000000:Int)≤(halfAngleBox bins 0 (3*groupSize)).shiftY).trans sy)))
  simp only [area,h1,h2,Nat.add_zero]

private theorem high {i j : Nat} (ij : i≤j) (ge : 9*groupSize≤i) (jn : j≤bins) :
    area walls (halfAngleBox bins i j)=0 := by
  obtain ⟨_xl,xh,yl,_yh⟩ := halfAngleBox_refines (by decide : 0<bins) ge ij jn le_rfl
  have sx : shiftX (halfAngleBox bins (9*groupSize) bins) ≤ shiftX (halfAngleBox bins i j) :=
    sub_le_sub_left xh _
  have h1 := empty_slice (d:=(halfAngleBox bins i j).xlo)
    (.inl (extrema.1.le.trans ((by decide : (500000000000:Int)≤(halfAngleBox bins (9*groupSize) bins).ylo).trans yl)))
  have h2 := empty_slice (lo:=(halfAngleBox bins i j).shiftY)
    (.inr (extrema.2.trans ((by decide : (971500000000:Int)≤shiftX (halfAngleBox bins (9*groupSize) bins)).trans sx)))
  simp only [area,h1,h2,Nat.add_zero]

/-- Only the six groups numbered 3 through 8 can carry a nonzero
partial-wave overlap. Both exterior families vanish by interval enclosure. -/
theorem tail_group {k : Nat} (hk : k<32) (out : k<3 ∨ 9≤k) : checkGroup k 0=true := by
  apply decide_eq_true
  change rangeSum (block walls) (k*128) 128 ≤ 0
  rw [rangeSum_spec]
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro i hi
  have il := Finset.mem_range.mp hi
  dsimp only [block]
  split_ifs with h
  · rfl
  · exfalso; apply h
    rcases out with lt|ge
    · apply low (Nat.le_add_right ..)
      dsimp [groupSize,blockSize]; omega
    · apply high (Nat.le_add_right ..)
      · dsimp [groupSize,blockSize]; omega
      · dsimp [bins,blockSize]; omega

end HadwigerNelson.Angular.Partial
