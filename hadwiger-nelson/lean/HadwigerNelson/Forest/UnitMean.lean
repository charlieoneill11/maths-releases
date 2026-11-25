import HadwigerNelson.Forest.UnitAngles
import HadwigerNelson.Crossings.UnitDegrees

namespace HadwigerNelson.Forest
open Placement MeasureTheory Set Centres Crossings
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem nonneg_cap {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {X : Finset Plane} (L : Layers X) (v : Plane) : 0≤headCap L Ω v :=
  (edgeShort_bounds sound L .r 0 v).1.trans (edgeShort_bounds sound L .r 0 v).2

private theorem sum_step_bounds {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    (M : ℝ) (hm : 0≤M) :
    let b := ∑ k:Fin 16384,unitStep Ω (k.val+1)
    let a := ∑ k:Fin 16384,max (unitStep Ω (k.val+1)-M) 0
    0≤a ∧ a≤b := by
  exact ⟨Finset.sum_nonneg (fun _ _ => le_max_right ..),Finset.sum_le_sum (fun k _ =>
    max_le (sub_le_self _ hm) (unitStep_nonneg sound _))⟩

theorem retention_bounds {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    (M : ℝ) (hm : 0≤M) : retention Ω M ∈ Icc 0 1 := by
  obtain ⟨p,q⟩ := sum_step_bounds sound M hm
  exact ⟨div_nonneg p (p.trans q),div_le_one_of_le₀ q (p.trans q)⟩

theorem retained_moment {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    (M : ℝ) (hm : 0≤M) :
    unitBin 1/Real.pi*(∑ k:Fin 16384,max (unitStep Ω (k.val+1)-M) 0) =
      (unitMean Ω/2)*retention Ω M := by
  obtain ⟨p,q⟩ := sum_step_bounds sound M hm
  unfold unitMean retention
  by_cases z : (∑ k:Fin 16384,unitStep Ω (k.val+1))=0
  · rw [z] at q ⊢
    simp [le_antisymm q p]
  · field_simp

private theorem pair_integral {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    (x y : Plane) (M : ℝ) (hm : 0≤M) :
    let g := fun θ => max (edgeUnit Ω θ x y-M) 0
    Integrable g (uniformInterval (2*Real.pi)) ∧
      (∫ θ,g θ ∂uniformInterval (2*Real.pi)) =
        if dist x y=1 then unitMean Ω/2*retention Ω M else 0 := by
  classical
  intro g
  by_cases pair : dist x y=1
  · obtain ⟨φ,hφ⟩ := unit_phase pair
    let f k := max (unitStep Ω k-M) 0
    have eq : g=fun θ => verticalWindow f (θ+φ) := by
      funext θ
      dsimp only [g]
      rw [edgeUnit_phase Ω (hφ θ)]
      unfold verticalWindow
      split
      · rfl
      · exact max_eq_right (by linarith)
    rw [eq,if_pos pair,verticalWindow_average,← retained_moment sound M hm]
    refine ⟨?_,rfl⟩
    exact verticalWindow_integrable_uniform f φ
  · have zero (θ) : g θ=0 := by
      have nc : ¬unitCandidate θ x y := fun h => pair (unitCandidate_unit h)
      simp [g,edgeUnit,nc,hm]
    rw [show g=fun _ => 0 from funext zero,if_neg pair]
    simp

/-- Deterministic degree accounting after taking the expectation of each orientation. -/
private theorem oriented_weights (X T : Finset Plane) (sub : T⊆X) (r : Plane → ℝ)
    (rr : ∀ y∈X,r y∈Icc 0 1) :
    (2:ℝ)*unitEdgeCount X -
      (∑ x∈X,((if x∈T then 0 else 1 : ℝ)+1-r x)*unitDegree X x)
      ≤ ∑ y∈X,∑ x∈T,if dist x y=1 then r y else 0 := by
  classical
  let miss x : ℝ := if x∈T then 0 else 1
  let adj (x y : Plane) (v : ℝ) := if dist x y=1 then v else 0
  have row (x) (v : ℝ) : (∑ y∈X,adj x y v) = (unitDegree X x:ℝ)*v := by
    simp [adj,unitDegree,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have column (y) (v : ℝ) : (∑ x∈X,adj x y v) = (unitDegree X y:ℝ)*v := by
    simpa only [adj,dist_comm _ y] using row y v
  have refund (x y : Plane) (hy : y∈X) : adj x y 1 - adj x y (miss x) - adj x y (1-r y) ≤
      (if x∈T then adj x y (r y) else 0) := by
    by_cases h : dist x y=1 <;> by_cases t : x∈T <;> simp [adj,miss,h,t]
    all_goals linarith [(rr y hy).1,(rr y hy).2]
  have hsum := Finset.sum_le_sum (s:=X) (fun y hy => Finset.sum_le_sum (s:=X) (fun x _ => refund x y hy))
  simp_rw [Finset.sum_sub_distrib] at hsum
  rw [Finset.sum_comm (s:=X) (t:=X) (f:=fun y x => adj x y (miss x))] at hsum
  simp_rw [row,column] at hsum
  have tset : X.filter (·∈T)=T := by ext x; simp; exact fun h => sub h
  simp_rw [← Finset.sum_filter,tset] at hsum
  have count : (∑ x∈X,(unitDegree X x:ℝ)) = 2*unitEdgeCount X := by exact_mod_cast sum_unitDegree X
  simp only [mul_one,count] at hsum
  have cost (x) : (miss x+1-r x)*unitDegree X x =
      (unitDegree X x:ℝ)*miss x+unitDegree X x*(1-r x) := by ring
  change _ - ∑ x∈X,(miss x+1-r x)*unitDegree X x ≤ _
  simp_rw [cost,Finset.sum_add_distrib]
  linarith only [hsum]

theorem expected_unit_credit (W : Wave.Datum) (Ω : ℝ → ℝ → ℝ) (sound : Wave.holeEnclosure W Ω)
    (X : Finset Plane) (L : Layers X) (m : Mode) :
    unitMean Ω * max 0 ((unitEdgeCount X : ℝ) -
      (∑ v∈X,((if v∈eligible L m then 0 else 1 : ℝ)+1-retention Ω (headCap L Ω v))*unitDegree X v/2)) ≤
    ∫ θ,(∑ y∈X,excessCredit L Ω m θ y) ∂uniformInterval (2*Real.pi) := by
  classical
  let T := eligible L m
  let r y := retention Ω (headCap L Ω y)
  let bb := unitMean Ω / 2
  have posB : 0≤unitMean Ω := mul_nonneg (by unfold unitBin w; positivity)
    (Finset.sum_nonneg fun _ _ => unitStep_nonneg sound _)
  have mom (y x : Plane) := pair_integral sound x y (headCap L Ω y) (nonneg_cap sound L y)
  have per (y : Plane) : (∫ θ,excessCredit L Ω m θ y ∂uniformInterval (2*Real.pi)) =
      bb*∑ x∈T,if dist x y=1 then r y else 0 := by
    unfold excessCredit
    rw [integral_finset_sum _ (fun x _ => (mom y x).1),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [(mom y x).2]
    by_cases near : dist x y=1 <;> simp [bb,r,near]
  have excInt (y : Plane) : Integrable (fun θ => excessCredit L Ω m θ y) (uniformInterval (2*Real.pi)) :=
    integrable_finset_sum (eligible L m) (fun x _ => (mom y x).1)
  rw [integral_finset_sum X (fun y _ => excInt y)]
  simp_rw [per]
  rw [← Finset.mul_sum]
  have sub : T ⊆ X := by
    cases m with
    | r => exact L.maximalR.1
    | d => exact L.maximalD.1.trans L.maximalR.1
    | centresOnly => exact Finset.empty_subset _
  have ww := oriented_weights X T sub r (fun y _ => retention_bounds sound _ (nonneg_cap sound L _))
  have nonnegative : 0 ≤ ∑ y∈X,∑ x∈T,if dist x y=1 then r y else 0 :=
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun _ _ => by
      split
      · exact (retention_bounds sound _ (nonneg_cap sound L y)).1
      · rfl
  rw [mul_max_of_nonneg _ _ posB,mul_zero]
  apply max_le (mul_nonneg (div_nonneg posB (by norm_num)) nonnegative)
  rw [← Finset.sum_div]
  have upper := mul_le_mul_of_nonneg_left ww (div_nonneg posB (by norm_num : (0:ℝ)≤2))
  dsimp only [bb,r,T] at upper ⊢
  linarith only [upper]

end
end HadwigerNelson.Forest
