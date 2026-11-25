import HadwigerNelson.Centres.Reserve
import HadwigerNelson.Centres.SingleThresholds

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem remainder_card (X Z : Finset Plane) :
    ((univ : Finset (Arc X))\arcsOn X Z).card = outsideDegree X Z := by
  have eq : (univ : Finset (Arc X))\arcsOn X Z = arcsOn X (X\Z) := by
    ext e; simp only [mem_sdiff,mem_univ,mem_arcsOn,true_and,(head e).property]
  rw [eq,card_arcsOn X _ sdiff_subset]; rfl

/-- Total remaining angle after the admissible reserves and the seven single-arc
charges, for any set of circles containing all the eligible heads. -/
theorem budget_on (X D Z : Finset Plane) (sub : Z ⊆ X) (heads : D ⊆ Z)
    (hd : minNonisolatedDegree X 3) {bR bD : ℝ} (hR : admissible X δR bR) (hD : admissible X δ bD)
    (s : Fin 7 → ℝ) (long : ∀ i, s i ≤ (longSingles X i).card) :
    orientExcess X D / 2 ≤ Real.pi*Z.card -
      (unitEdgeCount X-bR)*δR - (unitEdgeCount X-bD)*(δ-δR) + δ*(outsideDegree X Z:ℝ)/2 -
      (∑ i, excessWidth i * max (s i-outsideDegree X Z) 0)/2 := by
  let S := arcsOn X Z
  let o := outsideDegree X Z
  have rem : ((univ:Finset (Arc X))\S).card=o := remainder_card X Z
  have all := card_sdiff_add_card_eq_card (subset_univ S)
  rw [rem,card_all_arcs] at all
  have total : (o:ℝ)+(S.card:ℝ) = 2*unitEdgeCount X := by exact_mod_cast all
  have penalty (i : Fin 7) : excessWidth i * max (s i-o) 0 ≤
      ∑ e ∈ S, if e∈longSingles X i then excessWidth i else 0 := by
    let F := longSingles X i
    let I := S.filter (·∈F)
    have count := F.card_sdiff_add_card_inter S
    have missing : (F\S).card ≤ o := (card_le_card (sdiff_subset_sdiff (subset_univ F) (fun _ h ↦ h))).trans rem.le
    have ie : F∩S=I := by ext e; simp [I,and_comm]
    rw [ie] at count
    have all : ((F\S).card:ℝ) + I.card = F.card := by exact_mod_cast count
    have miss : ((F\S).card:ℝ) ≤ o := by exact_mod_cast missing
    have bound : max (s i-o) 0 ≤ I.card := max_le (by linarith only [all,miss,long i]) (by positivity)
    have eq : (∑ e ∈ S, if e∈F then excessWidth i else 0) = I.card*excessWidth i := by
      rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    rw [eq,mul_comm (excessWidth i)]
    exact mul_le_mul_of_nonneg_right bound (excess_nonneg i)
  have pens := Finset.sum_le_sum (s:=univ) (fun i _ ↦ penalty i)
  rw [Finset.sum_comm] at pens
  have res := reserve_sum_lower X S hd hR hD
  have orient := orientation_loss X D Z heads hd
  change orientExcess X D ≤ ∑ e∈S, loss e at orient
  simp only [loss,Finset.sum_sub_distrib] at orient
  have ang := angle_arcsOn X Z sub
  change ∑ e∈S, length e ≤ _ at ang
  change orientExcess X D / 2 ≤ Real.pi*Z.card - ((unitEdgeCount X:ℝ)-bR)*δR -
    ((unitEdgeCount X:ℝ)-bD)*(δ-δR) + δ*(o:ℝ)/2-(∑ i, excessWidth i*max (s i-(o:ℝ)) 0)/2
  have joint := orient.trans (sub_le_sub (sub_le_sub ang res) pens)
  calc
    _ ≤ (2*Real.pi*Z.card-(((S.card:ℝ)-2*bR)*δR+((S.card:ℝ)-2*bD)*(δ-δR)) -
        (∑ i, excessWidth i*max (s i-(o:ℝ)) 0))/2 := div_le_div_of_nonneg_right joint (by norm_num)
    _ = _ := by rw [show (S.card:ℝ)=2*unitEdgeCount X-(o:ℝ) by linarith only [total]]; ring

theorem physical_orientation_budgets (X D : Finset Plane) (hD : D ⊆ X) (sep : Packing.separated D δ)
    (hd : minNonisolatedDegree X 3) (bR bD : ℝ) (hR : admissible X δR bR)
    (hbD : admissible X δ bD) :
    let t : ℝ := doubledPairs X
    let LD : ℝ := outsideDegree X D
    t - bR - LD/2 ≤ ((orientationSet X D δR).card : ℝ)/2 ∧
    t - bD - LD/2 ≤ ((orientationSet X D δ).card : ℝ)/2 ∧
    (∑ z ∈ orientationSet X D δR, (arcLength X z.2 z.1 - if δ ≤ chord z.2 z.1 then δ else δR))/2 ≤
      angularBudget X.card (unitEdgeCount X) (doubledPairs X) (X.card-D.card) LD bR bD := by
  refine ⟨many_orientations X D δR bR hR hd,many_orientations X D δ bD hbD hd,?_⟩
  let s (i : Fin 7) : ℝ := 2*(unitEdgeCount X:ℝ)-2*(doubledPairs X:ℝ)-
      ((((diskLimit i-1)*D.card/2:ℕ):ℝ)+min (2*(outsideDegree X D:ℝ)) ((diskLimit i*(X.card-D.card)+(X.card-D.card).choose 2:ℕ):ℝ))
  have longs (i) : s i ≤ (longSingles X i).card := longSingles_lower X D hD sep hd i
  have full := budget_on X D X (fun _ h ↦ h) hD hd hR hbD s longs
  have part := budget_on X D D hD (fun _ h ↦ h) hd hR hbD s longs
  have hdcard := card_le_card hD
  have hcard : X.card-(X.card-D.card)=D.card := by omega
  have none : outsideDegree X X=0 := by simp [outsideDegree]
  simp only [none,Nat.cast_zero,sub_zero,mul_zero,zero_div,add_zero] at full
  unfold angularBudget
  dsimp only
  rw [hcard]
  change orientExcess X D/2 ≤ _
  apply le_min
  · simpa only [s] using full
  · rw [Nat.cast_sub hdcard]
    change _ ≤ (Real.pi*X.card - ((unitEdgeCount X:ℝ)-bR)*δR - ((unitEdgeCount X:ℝ)-bD)*(δ-δR) -
      Real.pi*((X.card:ℝ)-D.card) + δ*outsideDegree X D/2) - (∑ i, excessWidth i*max (s i-outsideDegree X D) 0)/2
    linarith only [part]

end
end HadwigerNelson.Centres
