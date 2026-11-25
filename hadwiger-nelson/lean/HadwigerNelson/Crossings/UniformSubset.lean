import HadwigerNelson.Crossings.Parameters
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Containment probabilities for a fixed pair or four distinct vertices in
the uniform fixed-size vertex sample of the crossing argument. -/

namespace HadwigerNelson.Crossings

theorem count_supersets {n k : Nat} (W : Finset (Fin n)) (hk : W.card ≤ k) (_hkn : k ≤ n) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => W ⊆ S)).card =
      (n-W.card).choose (k-W.card) := by
  classical
  have disj {T : Finset (Fin n)} (h : T ⊆ Wᶜ) : Disjoint T W :=
    Finset.disjoint_left.mpr fun x hx hxw => Finset.mem_compl.mp (h hx) hxw
  calc
    _ = ((Wᶜ).powersetCard (k-W.card)).card := by
      apply Finset.card_bij' (fun S _ => S \ W) (fun T _ => T ∪ W)
      · intro S h
        obtain ⟨hS,hW⟩ := Finset.mem_filter.mp h
        refine Finset.mem_powersetCard.mpr ⟨?_,?_⟩
        · exact fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
        · rw [Finset.card_sdiff_of_subset hW,(Finset.mem_powersetCard.mp hS).2]
      · intro T h
        obtain ⟨hT,ht⟩ := Finset.mem_powersetCard.mp h
        refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,
          Finset.subset_union_right⟩
        rw [Finset.card_union_of_disjoint (disj hT),ht,Nat.sub_add_cancel hk]
      · intro S h
        exact Finset.sdiff_union_of_subset (Finset.mem_filter.mp h).2
      · intro T h
        exact (Finset.union_sdiff_self T W).trans
          (Finset.sdiff_eq_self_of_disjoint (disj (Finset.mem_powersetCard.mp h).1))
    _ = _ := by simp [Finset.card_compl]

private theorem count_mul_desc {n k t : Nat} (ht : t ≤ k) :
    (((n-t).choose (k-t) : Nat) : ℝ)*(n.descFactorial t : ℝ) =
      (n.choose k : ℝ)*(k.descFactorial t : ℝ) := by
  exact_mod_cast (show (n-t).choose (k-t)*n.descFactorial t = n.choose k*k.descFactorial t by
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose]
    calc
      _ = t.factorial*(n.choose t*(n-t).choose (k-t)) := by ac_rfl
      _ = _ := by rw [← Nat.choose_mul ht]; ac_rfl)

private theorem desc_two {a : Nat} (ha : 4 ≤ a) :
    (a.descFactorial 2 : ℝ) = (a:ℝ)*(a-1 : ℝ) := by
  simp [Nat.descFactorial_succ, Nat.cast_sub (show 1≤a by omega)]
  ring

private theorem desc_four {a : Nat} (ha : 4 ≤ a) :
    (a.descFactorial 4 : ℝ) = (a:ℝ)*(a-1 : ℝ)*(a-2 : ℝ)*(a-3 : ℝ) := by
  simp [Nat.descFactorial_succ, Nat.cast_sub (show 1≤a by omega),
    Nat.cast_sub (show 2≤a by omega), Nat.cast_sub (show 3≤a by omega)]
  ring

theorem pair_count {n k : Nat} (hk : 4 ≤ k) (hn : k ≤ n) :
    (((n-2).choose (k-2) : Nat) : ℝ) = (n.choose k : ℝ)*pairProbability n k := by
  have n4 : (4:ℝ) ≤ n := by exact_mod_cast hk.trans hn
  have h := count_mul_desc (n:=n) (show 2≤k by omega)
  rw [desc_two (hk.trans hn),desc_two hk] at h
  unfold pairProbability
  rw [← mul_div_assoc]
  apply (eq_div_iff (mul_ne_zero (by linarith) (by linarith))).mpr
  exact h

theorem four_count {n k : Nat} (hk : 4 ≤ k) (hn : k ≤ n) :
    (((n-4).choose (k-4) : Nat) : ℝ) = (n.choose k : ℝ)*fourProbability n k := by
  have n4 : (4:ℝ) ≤ n := by exact_mod_cast hk.trans hn
  have h := count_mul_desc (n:=n) hk
  rw [desc_four (hk.trans hn),desc_four hk] at h
  have h0 : (n:ℝ) ≠ 0 := by linarith
  have h1 : (n:ℝ)-1 ≠ 0 := by linarith
  have h2 : (n:ℝ)-2 ≠ 0 := by linarith
  have h3 : (n:ℝ)-3 ≠ 0 := by linarith
  unfold fourProbability pairProbability
  field_simp [h0,h1,h2,h3]
  linear_combination h

end HadwigerNelson.Crossings
