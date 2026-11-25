import HadwigerNelson.Forest.CollisionAngles
import HadwigerNelson.Crossings.CircleIntersections

namespace HadwigerNelson.Forest
open Placement MeasureTheory Set Crossings Centres
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem edgeUnit_zero (Ω : ℝ → ℝ → ℝ) (θ : ℝ) {x y : Plane} (hn : dist x y≠1) : edgeUnit Ω θ x y = 0 := by
  have no : ¬unitCandidate θ x y := fun yes => hn (unitCandidate_unit yes)
  simp only [edgeUnit,if_neg no]

theorem edgeUnit_integrable (Ω : ℝ → ℝ → ℝ) (x y : Plane) :
    Integrable (fun θ => edgeUnit Ω θ x y) (uniformInterval (2*Real.pi)) := by
  by_cases h : dist x y=1
  · obtain ⟨φ,he⟩ := unit_phase h
    simp_rw [fun θ => edgeUnit_phase Ω (he θ)]
    exact verticalWindow_integrable_uniform _ _
  · have zero (θ : ℝ) : edgeUnit Ω θ x y=0 := edgeUnit_zero Ω θ h
    simp_rw [zero]; simp

private def flagged (D : Finset Plane) (u v : Plane) := u≠v ∧ ¬(u∈D ∧ v∈D)

private theorem even_pairs (R D : Finset Plane) (t : ℝ) :
    (∑ u∈R,∑ v∈R,if flagged D u v ∧ dist u v≤2*t then (1:ℝ) else 0)=2*neighbourPairs R D t := by
  classical
  letI : LinearOrder Plane := linearOrderOfSTO WellOrderingRel
  let n (u v : Plane) : ℕ := if flagged D u v ∧ dist u v≤2*t then 1 else 0
  let f (u v : Plane) : ℕ := if u<v then n u v else 0
  have symm (u v : Plane) : n v u=n u v := by
    simp only [n,flagged,dist_comm v u,(ne_comm : v≠u ↔ u≠v),(and_comm : v∈D ∧ u∈D ↔ u∈D ∧ v∈D)]
    split <;> simp_all
  have split (u v : Plane) : n u v=f u v+f v u := by
    rcases lt_trichotomy u v with lt|rfl|gt
    · simp [f,lt,lt.asymm]
    · simp [f,n,flagged]
    · simp [f,gt,gt.asymm,symm u v]
  have total : (∑ u∈R,∑ v∈R,n u v)=2*(∑ u∈R,∑ v∈R,f u v) := by
    simp_rw [split,Finset.sum_add_distrib]
    rw [Finset.sum_comm (f:=fun u v => f v u)]
    omega
  have row (u) : (∑ v∈R,n u v)=(R.filter (fun v => u≠v ∧ ¬(u∈D ∧ v∈D) ∧ dist u v≤2*t)).card := by
    simp only [n,flagged,and_assoc,Finset.sum_boole,Nat.cast_id]
  have nat : (∑ u∈R,∑ v∈R,n u v)=2*neighbourPairs R D t := by
    unfold neighbourPairs
    simp_rw [← row]
    omega
  calc _ = ((∑ u∈R,∑ v∈R,n u v : ℕ):ℝ) := by
         push_cast
         apply Finset.sum_congr rfl; intro u _
         apply Finset.sum_congr rfl; intro v _
         by_cases yes : flagged D u v ∧ dist u v≤2*t <;> simp [n,yes]
       _ = _ := by exact_mod_cast nat

private def lossTerm (Ω : ℝ → ℝ → ℝ) (D : Finset Plane) (y u v : Plane) (θ : ℝ) : ℝ :=
  if flagged D u v then min (edgeUnit Ω θ u y) (edgeUnit Ω θ v y) else 0

private theorem lossTerm_int (Ω : ℝ → ℝ → ℝ) (D : Finset Plane) (y u v : Plane) :
    Integrable (lossTerm Ω D y u v) (uniformInterval (2*Real.pi)) := by
  change Integrable (fun θ => if flagged D u v then min (edgeUnit Ω θ u y) (edgeUnit Ω θ v y) else 0) _
  by_cases h : flagged D u v
  · simp only [if_pos h]; exact (edgeUnit_integrable Ω u y).inf (edgeUnit_integrable Ω v y)
  · simp only [if_neg h]; exact integrable_const _

private theorem loss_eq {X : Finset Plane} (L : Layers X) (Ω : ℝ → ℝ → ℝ) (m : Mode) (y : Plane) (θ : ℝ) :
    collisionLoss L Ω m θ y=(∑ u∈eligible L m,∑ v∈eligible L m,lossTerm Ω L.D y u v θ)/2 := by
  unfold collisionLoss lossTerm flagged
  congr 1
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  by_cases yes : u≠v ∧ ¬(u∈L.D ∧ v∈L.D) <;> simp only [yes,if_true,if_false]

theorem collisionLoss_int {X : Finset Plane} (L : Layers X) (Ω : ℝ → ℝ → ℝ) (m : Mode) (y : Plane) :
    Integrable (fun θ => collisionLoss L Ω m θ y) (uniformInterval (2*Real.pi)) := by
  have comm (θ u v) : (if u≠v ∧ ¬(u∈L.D ∧ v∈L.D) then min (edgeUnit Ω θ u y) (edgeUnit Ω θ v y) else 0) =
      lossTerm Ω L.D y u v θ := by unfold lossTerm flagged; split <;> simp_all only [if_pos,if_neg]
  simp only [collisionLoss,comm]
  exact (integrable_finset_sum (eligible L m) (fun u _ => integrable_finset_sum (eligible L m)
    (fun v _ => lossTerm_int Ω L.D y u v))).div_const 2

private theorem column_bound (W : Wave.Datum) (Ω : ℝ → ℝ → ℝ) (sound : Wave.holeEnclosure W Ω)
    (X D : Finset Plane) (u v : Plane) :
    let t (k : Fin 16384) := unitBin (k.val+1)
    let h (k : Fin 16384) := unitStep Ω (k.val+1)
    (∑ y∈X,∫ θ,lossTerm Ω D y u v θ ∂uniformInterval (2*Real.pi)) ≤
      2*(unitBin 1/Real.pi)*(∑ k:Fin 16384,if flagged D u v ∧ dist u v≤2*t k then h k else 0) := by
  intro t h
  by_cases fl : flagged D u v
  · let C := X.filter fun y => dist y u=1 ∧ dist y v=1
    obtain ⟨Z,size,spec⟩ := unit_intersections_le_two u v fl.1
    have bound : C.card≤2 := (Finset.card_le_card (t:=Z) (fun y hy => (spec y).mpr (Finset.mem_filter.mp hy).2)).trans size
    let K := unitBin 1/Real.pi * (∑ k:Fin 16384,if dist u v≤2*t k then h k else 0)
    have kn : 0≤K := mul_nonneg (by unfold unitBin w; positivity) (Finset.sum_nonneg fun k _ => by
      split <;> first | exact unitStep_nonneg sound _ | rfl)
    have each (y) (hy : y∈X) : (∫ θ,lossTerm Ω D y u v θ ∂uniformInterval (2*Real.pi)) ≤ if y∈C then K else 0 := by
      by_cases yes : y∈C
      · rw [if_pos yes]; obtain ⟨hu,hv⟩ := (Finset.mem_filter.mp yes).2
        simpa only [lossTerm,if_pos fl] using collision_mean W Ω sound u v y fl.1 ((dist_comm ..).trans hu) ((dist_comm ..).trans hv)
      · rw [if_neg yes]
        by_cases both : dist y u=1 ∧ dist y v=1
        · exact (yes (Finset.mem_filter.mpr ⟨hy,both⟩)).elim
        · have zero (θ) : lossTerm Ω D y u v θ=0 := by
            rw [lossTerm,if_pos fl]
            rcases not_and_or.mp both with hu|hv
            · rw [show edgeUnit Ω θ u y=0 from edgeUnit_zero Ω θ (fun h => hu ((dist_comm ..).trans h))]
              exact min_eq_left (edgeUnit_nonneg sound ..)
            · rw [show edgeUnit Ω θ v y=0 from edgeUnit_zero Ω θ (fun h => hv ((dist_comm ..).trans h))]
              exact min_eq_right (edgeUnit_nonneg sound ..)
          simp_rw [zero]; simp
    have sum := Finset.sum_le_sum (s:=X) (fun y hy => each y hy)
    have inside : X.filter (·∈C)=C := by ext y; simp [C,and_assoc]
    simp only [← Finset.sum_filter,inside,Finset.sum_const,nsmul_eq_mul] at sum
    have cmp := mul_le_mul_of_nonneg_right (show (C.card:ℝ)≤2 by exact_mod_cast bound) kn
    simp only [fl,true_and]
    exact (sum.trans cmp).trans_eq (by dsimp [K]; ring)
  · simp [lossTerm,fl]

attribute [local irreducible] unitStep neighbourPairs

theorem collisionR_total (W : Wave.Datum) (Ω : ℝ → ℝ → ℝ) (sound : Wave.holeEnclosure W Ω)
    (X : Finset Plane) (L : Layers X) :
    (∫ θ,∑ y∈X,collisionLoss L Ω .r θ y ∂uniformInterval (2*Real.pi)) ≤
      2*unitBin 1/Real.pi*(∑ k:Fin 16384,unitStep Ω (k.val+1)*neighbourPairs L.R L.D (unitBin (k.val+1))) := by
  let μ := uniformInterval (2*Real.pi)
  let F := fun u v y => lossTerm Ω L.D y u v
  let t (k : Fin 16384) := unitBin (k.val+1)
  let h (k : Fin 16384) := unitStep Ω (k.val+1)
  let c := 2*(unitBin 1/Real.pi)
  let Q (k : Fin 16384) (u v : Plane) := if flagged L.D u v ∧ dist u v≤2*t k then h k else 0
  have iv (u v y) : Integrable (F u v y) μ := lossTerm_int ..
  have expand (y) : (∫ θ,collisionLoss L Ω .r θ y ∂μ) =
      (∑ u∈L.R,∑ v∈L.R,∫ θ,F u v y θ ∂μ)/2 := by
    simp_rw [loss_eq]
    change (∫ θ,(∑ u∈L.R,∑ v∈L.R,F u v y θ)/2 ∂μ)=_
    rw [integral_div,integral_finset_sum L.R (fun u _ => integrable_finset_sum L.R (fun v _ => iv u v y))]
    simp_rw [fun u => integral_finset_sum L.R (fun v _ => iv u v y)]
  have flip : (∑ y∈X,∑ u∈L.R,∑ v∈L.R,∫ θ,F u v y θ ∂μ)=
      ∑ u∈L.R,∑ v∈L.R,∑ y∈X,∫ θ,F u v y θ ∂μ := by
    rw [Finset.sum_comm (s:=X) (t:=L.R)]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have bound := Finset.sum_le_sum (s:=L.R) (fun u _ => Finset.sum_le_sum (s:=L.R)
    (fun v _ => column_bound W Ω sound X L.D u v))
  change (∑ u∈L.R,∑ v∈L.R,∑ y∈X,∫ θ,F u v y θ ∂μ) ≤ ∑ u∈L.R,∑ v∈L.R,c*(∑ k,Q k u v) at bound
  have eval (k) : (∑ u∈L.R,∑ v∈L.R,Q k u v)=h k*(2*neighbourPairs L.R L.D (t k)) := by
    rw [← even_pairs,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases yes : flagged L.D u v ∧ dist u v≤2*t k <;> simp [Q,yes]
  have collect : (∑ u∈L.R,∑ v∈L.R,c*(∑ k,Q k u v)) =
      c*(∑ k,h k*(2*neighbourPairs L.R L.D (t k))) := by
    simp_rw [← Finset.mul_sum,← eval]
    apply congrArg (fun x : ℝ=>c*x)
    calc _ = ∑ u∈L.R,∑ k,∑ v∈L.R,Q k u v := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
         _ = _ := Finset.sum_comm
  rw [collect] at bound
  change (∫ θ,∑ y∈X,collisionLoss L Ω .r θ y ∂μ)≤_
  have outer : (∫ θ,∑ y∈X,collisionLoss L Ω .r θ y ∂μ) = ∑ y∈X, (∑ u∈L.R,∑ v∈L.R,∫ θ,F u v y θ ∂μ)/2 := by
    rw [integral_finset_sum X (fun y _ => collisionLoss_int L Ω .r y)]
    exact Finset.sum_congr rfl (fun y _ => expand y)
  rw [outer]
  rw [← Finset.sum_div,flip]
  apply (div_le_div_of_nonneg_right bound (by norm_num : (0:ℝ)≤2)).trans_eq
  dsimp only [c,t,h]
  simp only [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem collision_inner_zero {X : Finset Plane} (L : Layers X) (Ω : ℝ → ℝ → ℝ) (θ : ℝ) (y : Plane) :
    collisionLoss L Ω .d θ y=0 := by
  unfold collisionLoss
  simp only [eligible,div_eq_zero_iff,OfNat.ofNat_ne_zero,or_false]
  apply Finset.sum_eq_zero; intro u hu
  apply Finset.sum_eq_zero; intro v hv
  simp [hu,hv]

end
end HadwigerNelson.Forest
