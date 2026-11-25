import HadwigerNelson.Centres.CreditAlgebra
import HadwigerNelson.Centres.Admissible

namespace HadwigerNelson.Centres
open Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem sum_probabilities (X D : Finset Plane) (p : Profile) (F : Plane×Plane → ℝ)
    (prob : ∀ z ∈ orientationSet X D δR,
      (if δ≤chord z.2 z.1 then (intercept p-angleCost p*(arcLength X z.2 z.1-δ))/2
        else (smallIntercept p-angleCost p*(arcLength X z.2 z.1-δR))/2) ≤ F z) :
    smallIntercept p * ((orientationSet X D δR).card/2:ℝ) +
      (intercept p-smallIntercept p)*((orientationSet X D δ).card/2:ℝ) -
      angleCost p*((∑ z∈orientationSet X D δR,(arcLength X z.2 z.1 - if δ≤chord z.2 z.1 then δ else δR))/2)
      ≤ ∑ z∈orientationSet X D δR,F z := by
  let S := orientationSet X D δR
  let T := orientationSet X D δ
  let P (z : Plane×Plane) := δ≤chord z.2 z.1
  let e (z : Plane×Plane) := arcLength X z.2 z.1 - if P z then δ else δR
  have cut : S.filter P = T := by
    ext z
    simp only [S,T,P,orientationSet,Finset.mem_filter]
    constructor
    · rintro ⟨⟨xs,ho,_⟩,le⟩; exact ⟨xs,ho,le⟩
    · rintro ⟨xs,ho,le⟩; exact ⟨⟨xs,ho,(by norm_num [δ,δR] : δR≤δ).trans le⟩,le⟩
  have point (z) (hz : z∈S) :
      smallIntercept p+(if P z then intercept p-smallIntercept p else 0)-angleCost p*e z ≤ 2*F z := by
    have b := prob z hz
    by_cases c : P z
    · simp only [e,P,c,if_true] at b ⊢
      linear_combination 2*b
    · simp only [e,P,c,if_false,add_zero] at b ⊢
      linear_combination 2*b
  have sum := Finset.sum_le_sum point
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at sum
  have counts : (∑ z∈S,if P z then intercept p-smallIntercept p else 0) =
      T.card*(intercept p-smallIntercept p) := by
    rw [← Finset.sum_filter,cut,Finset.sum_const,nsmul_eq_mul]
  rw [counts] at sum
  change smallIntercept p*(S.card/2:ℝ)+(intercept p-smallIntercept p)*(T.card/2:ℝ)-
    angleCost p*((∑ z∈S,e z)/2) ≤ ∑ z∈S,F z
  linarith only [sum]

private theorem outside_le (facts : CitedFacts) (X D : Finset Plane)
    (hn : 2090≤X.card) (hd : minNonisolatedDegree X 3) (sub : D⊆X) :
    (outsideDegree X D:ℝ) ≤ degreeCap X.card (unitEdgeCount X) (X.card-D.card) := by
  have w := weighted_degree_upper facts X (X\D) ∅ 1 0 hn hd Finset.sdiff_subset
    (Finset.empty_subset _) (Finset.disjoint_empty_right _) zero_le_one le_rfl
  simpa only [outsideDegree,Nat.cast_sum,Finset.card_sdiff_of_subset sub,Finset.card_empty,
    Nat.cast_zero,zero_mul,one_mul,add_zero,degreeCap] using w

private theorem admissible_up {X : Finset Plane} {r a b : ℝ} (h : admissible X r a) (le : a≤b) :
    admissible X r b := ⟨h.1.trans le,h.2.1.trans le,h.2.2.trans (by linarith)⟩

/-- Proposition 52 reduces the numerical centre score to the orientation
counts and angular excess bound in Lemma 51 and to the probability
of each realized orientation in Lemma 49. -/
theorem credit_from_estimates (facts : CitedFacts) (X R D : Finset Plane)
    (hn : 2090≤X.card) (hd : minNonisolatedDegree X 3) (hR : Forest.maximalSeparated X R δR)
    (hD : Forest.maximalSeparated R D δ) (p : Profile) (F : Plane×Plane → ℝ)
    (pos : ∀ z, 0≤F z)
    (prob : ∀ z, orientation X D z.1 z.2 → δR≤chord z.2 z.1 →
      (if δ≤chord z.2 z.1 then (intercept p-angleCost p*(arcLength X z.2 z.1-δ))/2
        else (smallIntercept p-angleCost p*(arcLength X z.2 z.1-δR))/2) ≤ F z)
    (bounds : ∀ bR bD : ℝ, admissible X δR bR → admissible X δ bD →
      let t : ℝ := doubledPairs X
      let L : ℝ := outsideDegree X D
      t-bR-L/2 ≤ ((orientationSet X D δR).card:ℝ)/2 ∧
      t-bD-L/2 ≤ ((orientationSet X D δ).card:ℝ)/2 ∧
      (∑ z∈orientationSet X D δR,(arcLength X z.2 z.1 - if δ≤chord z.2 z.1 then δ else δR))/2
        ≤ angularBudget X.card (unitEdgeCount X) (doubledPairs X) (X.card-D.card) L bR bD) :
    profileCredit X.card (unitEdgeCount X) (X.card-R.card) (R.card-D.card)
      (intercept p) (smallIntercept p) (angleCost p) ≤ ∑ z∈orientationSet X D δR,F z := by
  let n := X.card
  let m := unitEdgeCount X
  let s := X.card-R.card
  let j := R.card-D.card
  have dsub := hD.1.trans hR.1
  have rd := Finset.card_le_card hR.1
  have dd := Finset.card_le_card hD.1
  have eq : X.card-D.card=s+j := by dsimp [s,j]; omega
  have lR : (outsideDegree X R : ℝ)≤degreeCap n m s := outside_le facts X R hn hd hR.1
  have lD := outside_le facts X D hn hd dsub
  rw [eq] at lD
  obtain ⟨a,b⟩ := physical_admissible_budgets X R D hR hD
  have ar : admissible X δR (budgetR n m s) := admissible_up a
    (min_le_min lR (min_le_min_left _ (div_le_div_of_nonneg_right (add_le_add lR le_rfl) (by norm_num))))
  have ad : admissible X δ (budgetD n m s j) := admissible_up b
    (min_le_min lD (min_le_min_left _ (by
      rw [Nat.cast_add]; exact div_le_div_of_nonneg_right (add_le_add lD le_rfl) (by norm_num))))
  obtain ⟨ca,cb,u⟩ := bounds _ _ ar ad
  rw [eq] at u
  have low := doubled_pairs_lower facts X (by omega) hd
  have le : pairLower n m≤doubledPairs X := by
    unfold pairLower
    exact_mod_cast low
  apply score_from_orientation n m s j _ p _ _ _ _ _ (by dsimp [s,j,n]; omega) lD le ca cb u
    (by positivity) (by positivity) (Finset.sum_nonneg fun z _ => pos z)
  apply sum_probabilities
  intro z hz
  have h := (Finset.mem_filter.mp hz).2
  exact prob z h.1 h.2

end
end HadwigerNelson.Centres
