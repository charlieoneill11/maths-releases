import HadwigerNelson.Centres.ThresholdDefs
import HadwigerNelson.Centres.ArcIncidences
import Mathlib.Tactic.FinCases

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

def reserve (l : ℝ) : ℝ := (if δR ≤ l then δR else 0) + (if δ ≤ l then δ-δR else 0)

theorem reserve_eq {l : ℝ} (lo : δR ≤ l) : reserve l = if δ ≤ l then δ else δR := by
  unfold reserve; rw [if_pos lo]; split <;> ring

theorem reserve_low (l : ℝ) (h : 0 ≤ l) : reserve l ≤ l := by
  unfold reserve; split_ifs <;> norm_num [δ,δR] at * <;> linarith

theorem excess_nonneg (i : Fin 7) : 0≤excessWidth i := by fin_cases i <;> norm_num [excessWidth]

theorem reserve_threshold (l : ℝ) (hl : 0 ≤ l) :
    reserve l + (∑ i : Fin 7, if threshold i ≤ l then excessWidth i else 0) ≤ l := by
  let t (i : ℕ) : ℝ := if i=0 then δ else (9+5*(i:ℝ))*δ/10
  have first : reserve l ≤ min l (t 0) := by
    apply le_min (reserve_low l hl)
    unfold reserve
    split_ifs <;> norm_num [t,δR,δ] at * <;> linarith
  have step (i : Fin 7) : (if threshold i≤l then excessWidth i else 0) ≤
      min l (t (i.val+1))-min l (t i.val) := by
    have a : t (i.val+1) = threshold i := by simp [t,threshold,tenths]; ring
    have b : t (i.val+1)-t i.val = excessWidth i := by fin_cases i <;> norm_num [t,excessWidth,δ]
    have ord : t i.val ≤ t (i.val+1) := by linarith [excess_nonneg i]
    by_cases low : threshold i ≤ l
    · rw [if_pos low,←b,min_eq_right (a ▸ low),min_eq_right (ord.trans (a ▸ low))]
    · rw [if_neg low]; exact sub_nonneg.mpr (min_le_min_left l ord)
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ ↦ step i)
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ min l (t (n+1))-min l (t n)),Finset.sum_range_sub (fun n ↦ min l (t n)) 7] at sum
  linarith only [first,sum,min_le_left l (t 7)]

def loss {X : Finset Plane} (e : Arc X) : ℝ :=
  length e - reserve (dist (start e) (finish e)) -
    ∑ i, if e ∈ longSingles X i then excessWidth i else 0

theorem loss_nonneg {X : Finset Plane} (hd : minNonisolatedDegree X 3) (e : Arc X) : 0 ≤ loss e := by
  have le := length_ge_chord hd e
  have a := reserve_threshold (dist (start e) (finish e)) dist_nonneg
  unfold loss
  by_cases yes : paired e
  · have no (i) : e ∉ longSingles X i := fun h ↦ (mem_filter.mp h).2.1 yes
    simp only [if_neg (no _),Finset.sum_const_zero,sub_zero]
    linarith [reserve_low (dist (start e) (finish e)) dist_nonneg]
  · have eq (i) : e∈longSingles X i ↔ threshold i ≤ dist (start e) (finish e) := by simp [longSingles,yes]
    simp_rw [eq]; linarith

def orientExcess (X D : Finset Plane) : ℝ :=
  ∑ z ∈ orientationSet X D δR, (arcLength X z.2 z.1 - if δ ≤ chord z.2 z.1 then δ else δR)

theorem orientation_loss (X D Z : Finset Plane) (sub : D ⊆ Z) (hd : minNonisolatedDegree X 3) :
    orientExcess X D ≤ ∑ e ∈ arcsOn X Z, loss e := by
  let O := orientationSet X D δR
  let physical (z : ↥O) : orientation X D z.val.1 z.val.2 := (mem_filter.mp z.property).2.1
  let f (z : ↥O) := assigned (physical z)
  have inj : Function.Injective f := fun p q h ↦ Subtype.ext (assigned_inj hd (physical p) (physical q) h)
  let I := (univ : Finset ↥O).image f
  have incl : I ⊆ arcsOn X Z := by
    intro e he; obtain ⟨z,_,rfl⟩ := mem_image.mp he
    apply mem_arcsOn.mpr
    rw [show (head (f z):Plane)=z.val.2 from (assigned_spec (physical z)).1]
    exact sub (physical z).2.1
  have le (z : ↥O) : arcLength X z.val.2 z.val.1-(if δ≤chord z.val.2 z.val.1 then δ else δR) ≤ loss (f z) := by
    have yes := assigned_paired (physical z)
    have no (i) : f z ∉ longSingles X i := fun h ↦ (mem_filter.mp h).2.1 yes
    have cut := (mem_filter.mp z.property).2.2
    have he := assigned_chord hd (physical z)
    change chord z.val.2 z.val.1 = dist (start (f z)) (finish (f z)) at he
    simp only [loss,if_neg (no _),Finset.sum_const_zero,sub_zero,←he,reserve_eq cut]
    exact sub_le_sub_right (assigned_length hd (physical z)) _
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun z _ ↦ le z)
  have eq : (∑ z : ↥O, loss (f z))=∑ e ∈ I, loss e := (Finset.sum_image inj.injOn).symm
  rw [eq] at total
  have suble := Finset.sum_le_sum_of_subset_of_nonneg incl (fun e _ _ ↦ loss_nonneg hd e)
  have r : (∑ z : ↥O, (arcLength X z.val.2 z.val.1 - if δ ≤ chord z.val.2 z.val.1 then δ else δR)) = orientExcess X D :=
    Finset.sum_attach O (fun z : Plane×Plane ↦ arcLength X z.2 z.1 - if δ ≤ chord z.2 z.1 then δ else δR)
  exact r ▸ total.trans suble

theorem reserve_sum_lower (X : Finset Plane) (S : Finset (Arc X)) (hd : minNonisolatedDegree X 3) {bR bD : ℝ}
    (hR : admissible X δR bR) (hD : admissible X δ bD) :
    ((S.card:ℝ)-2*bR)*δR+((S.card:ℝ)-2*bD)*(δ-δR) ≤ ∑ e ∈ S, reserve (dist (start e) (finish e)) := by
  let l (e : Arc X) := dist (start e) (finish e)
  have one (r b c : ℝ) (hc : 0≤c) (h : admissible X r b) :
      ((S.card:ℝ)-2*b)*c ≤ ∑ e ∈ S, if r ≤ l e then c else 0 := by
    have inc : S.filter (fun e ↦ l e < r) ⊆ (univ : Finset (Arc X)).filter (fun e ↦ l e < r) := by
      intro e he; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
    have small := (card_le_card inc).trans (card_short_arcs_le X hd r)
    have split := S.card_filter_add_card_filter_not (fun e ↦ r ≤ l e)
    simp only [not_le] at split
    have big : (S.card:ℝ)-2*b ≤ (S.filter (fun e ↦ r ≤ l e)).card := by
      have cast := (by exact_mod_cast small : ((S.filter fun e ↦ l e < r).card:ℝ) ≤ shortArcCount X r)
      have add := (by exact_mod_cast split : ((S.filter fun e ↦ r ≤ l e).card:ℝ)+(S.filter fun e ↦ l e < r).card=S.card)
      linarith [h.2.2]
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right big hc
  unfold reserve; rw [Finset.sum_add_distrib]
  exact add_le_add (one δR bR δR (by norm_num [δR]) hR) (one δ bD (δ-δR) (by norm_num [δ,δR]) hD)

end
end HadwigerNelson.Centres
