import HadwigerNelson.Angular.Checker

namespace HadwigerNelson.Angular

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem ordinate_upper : ∀ i : Fin 2049, CompleteWave.ordinate i ≤ 971000000000 := by
  decide +kernel

theorem tree_extrema (widths : Array Nat) (step depth first : Nat) (upper : Int)
    (hu : ∀ i, first ≤ i → i ≤ first+2^depth → (widths[i]?.getD 0:Int) ≤ upper) :
    (tabulate widths step depth first).stats.stop = ((first+2^depth)*step:Nat) ∧
    (tabulate widths step depth first).stats.high ≤ upper := by
  induction depth generalizing first with
  | zero =>
    constructor
    · change ((first:Int)+1)*step = ↑((first+2^0)*step:Nat)
      simp
    · exact max_le (hu first le_rfl (by omega)) (hu (first+1) (by omega) (by simp))
  | succ depth ih =>
    have e : first+2^(depth+1) = first+2^depth+2^depth := by rw [pow_succ]; omega
    have a := ih first (fun i hi hv => hu i hi (by omega))
    have b := ih (first+2^depth) (fun i hi hv => hu i (by omega) (by omega))
    constructor
    · change max _ _ = _
      rw [a.1,b.1,e]
      apply max_eq_right
      exact_mod_cast Nat.mul_le_mul_right step (Nat.le_add_right (first+2^depth) (2^depth))
    · exact max_le a.2 b.2

private abbrev tree := tabulate CompleteWave.profile CompleteWave.step 11 0

private theorem extrema : tree.stats.stop = (500000000000:Int) ∧
    tree.stats.high ≤ (971000000000:Int) := by
  apply tree_extrema
  intro i _ hi
  have h : i < 2049 := by omega
  simp only [CompleteWave.profile,Array.getElem?_map,Array.getElem?_range,h,↓reduceIte,
    Option.map_some,Option.getD_some]
  exact_mod_cast ordinate_upper ⟨i,h⟩

theorem misses_of_extreme (t : Segments) (d lo : Int)
    (h : t.stats.stop ≤ lo ∨ t.stats.high ≤ d) : t.misses d lo := by
  cases t with
  | single s => exact decide_eq_true h
  | branch v a b =>
    simp only [Segments.misses,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inl h

private theorem low_tail : skipped tree (halfAngleBox (2^28) 0 (3*2^23)) := by
  simp only [skipped,Bool.and_eq_true]
  exact ⟨misses_of_extreme _ _ _ (.inr (extrema.2.trans (by decide))),
    misses_of_extreme _ _ _ (.inl (extrema.1.le.trans (by decide)))⟩

private theorem high_tail : skipped tree (halfAngleBox (2^28) (9*2^23) (2^28)) := by
  simp only [skipped,Bool.and_eq_true]
  exact ⟨misses_of_extreme _ _ _ (.inl (extrema.1.le.trans (by decide))),
    misses_of_extreme _ _ _ (.inr (extrema.2.trans (by decide)))⟩

/-- Both displacement areas vanish throughout either outer range, so the
26 groups they contain require no native evaluation. -/
theorem tail_group {k : Nat} (hk : k < 32) (out : k < 3 ∨ 9 ≤ k) :
    checkGroup k 0 = true := by
  apply decide_eq_true
  change rangeSum (blockSum tree (2^28) (2^16)) (k*128) 128 ≤ 0
  rw [rangeSum_from_blocks tree (tabulate_valid _ _ (by decide) _ _) (by decide : 0<2^28)
    (by omega : (k*128+128)*2^16 ≤ 2^28),rangeSum_spec]
  have z : ∀ i ∈ Finset.range (128*2^16), weightedBin tree (2^28) (k*128*2^16+i) = 0 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rcases out with lt|ge
    · exact weightedBin_zero_of_skipped tree (tabulate_valid _ _ (by decide) _ _)
        (by decide) (Nat.zero_le _) (by omega) (by decide) low_tail
    · exact weightedBin_zero_of_skipped tree (tabulate_valid _ _ (by decide) _ _)
        (by decide) (by omega) (by omega) le_rfl high_tail
  rw [Finset.sum_eq_zero z]

end HadwigerNelson.Angular
