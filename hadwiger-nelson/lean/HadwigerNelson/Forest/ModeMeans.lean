import HadwigerNelson.Forest.ShortMean
import HadwigerNelson.Forest.UnitMean
import HadwigerNelson.Blueprint.Point.Crossings

namespace HadwigerNelson.Forest
open MeasureTheory Set Placement Crossings Centres
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem layers_for (X R D : Finset Plane) (hR : maximalSeparated X R δR) (hD : maximalSeparated R D δ) :
    ∃ L : Layers X,L.R=R ∧ L.D=D := by
  classical
  let outer x := if h : x∈X ∧ x∉R then (hR.2.2 x h.1 h.2).choose else x
  let inner x := if h : x∈R ∧ x∉D then (hD.2.2 x h.1 h.2).choose else x
  let parent x := if x∈R then inner x else outer x
  refine ⟨⟨R,D,hR,hD,parent,?_,?_,?_⟩,rfl,rfl⟩
  · intro x hx nr; simpa only [parent,if_neg nr,outer,dif_pos (And.intro hx nr)] using (hR.2.2 x hx nr).choose_spec
  · intro x hx nd; simpa only [parent,if_pos hx,inner,dif_pos (And.intro hx nd)] using (hD.2.2 x hx nd).choose_spec
  · intro x hx; simp [parent,hD.1 hx,inner,hx]

private theorem positive_total (Ω : ℝ → ℝ → ℝ) (h : 0<unitMean Ω) :
    (∑ k:Fin 16384,unitStep Ω (k.val+1)) ≠ 0 := by
  intro z
  simp [unitMean,z] at h

private theorem retention_zero {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    (h : 0<unitMean Ω) : retention Ω 0=1 := by
  simp only [retention,sub_zero,fun k => max_eq_left (unitStep_nonneg sound (k+1)),div_self (positive_total Ω h)]

theorem short_integrable {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {X : Finset Plane} (L : Layers X) (m : Mode) (y : Plane) :
    Integrable (fun θ => edgeShort L Ω m θ y) (uniformInterval (2*Real.pi)) := by
  have meas : Measurable (fun θ => edgeShort L Ω m θ y) := by
    by_cases off : m=.centresOnly ∨ y∈L.D
    · simp [edgeShort,off]
    simp only [edgeShort,if_neg off]
    apply (measurable_of_countable (cappedShort Ω _)).comp
    let z (θ : ℝ) := rotate θ (y-L.parent y)
    have cz : Continuous z := by unfold z rotate; fun_prop
    have c0 := ((PiLp.continuous_apply 2 _ 0).comp cz).abs.measurable
    have c1 := ((PiLp.continuous_apply 2 _ 1).comp cz).abs.measurable
    have cn := cz.norm.measurable
    change Measurable (fun θ => min 8191 ⌊8192*|z θ 1|/(‖z θ‖+|z θ 0|)⌋₊)
    exact measurable_const.min (((measurable_const.mul c1).div (cn.add c0)).nat_floor)
  exact Integrable.of_mem_Icc 0 (headCap L Ω y) meas.aemeasurable
    (Filter.Eventually.of_forall fun θ => edgeShort_bounds sound L m θ y)

theorem excess_integrable {X : Finset Plane} (L : Layers X) (Ω : ℝ → ℝ → ℝ) (m : Mode) (y : Plane)
    (ei : ∀ x,Integrable (fun θ => edgeUnit Ω θ x y) (uniformInterval (2*Real.pi))) :
    Integrable (fun θ => excessCredit L Ω m θ y) (uniformInterval (2*Real.pi)) :=
  integrable_finset_sum (eligible L m) (fun x _ => ((ei x).sub (integrable_const _)).sup (integrable_const 0))

theorem short_payment {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {X : Finset Plane} (L : Layers X) (m : Mode) (on : m ≠ .centresOnly) (C E : ℝ)
    (low : C≤lowerShortMean Ω a) (inner : E≤lowerShortMean Ω d) :
    ((X.card-L.R.card : ℕ):ℝ)*C + ((L.R.card-L.D.card : ℕ):ℝ)*E ≤
      ∫ θ,∑ y∈X,edgeShort L Ω m θ y ∂uniformInterval (2*Real.pi) := by
  let U := X\L.R
  let J := L.R\L.D
  have same (θ y) : edgeShort L Ω m θ y=edgeShort L Ω .r θ y := by simp [edgeShort,on]
  have each (y) (hy : y∈X) :
      (if y∈U then C else 0) + (if y∈J then E else 0) ≤ ∫ θ,edgeShort L Ω m θ y ∂uniformInterval (2*Real.pi) := by
    simp_rw [same]
    by_cases root : y∈L.D
    · simp [U,J,hy,root,L.maximalD.1 root,edgeShort]
    obtain ⟨ineq,eq⟩ := averaged_short_parent W Ω sound X L y hy root
    rw [eq]
    by_cases inside : y∈L.R
    · simpa [U,J,root,inside,hy] using inner.trans (by simpa [inside] using ineq)
    · simpa [U,J,root,inside,hy] using low.trans (by simpa [inside] using ineq)
  have rsub := L.maximalR.1
  have dsub := L.maximalD.1
  have filterU : X.filter (·∈U)=U := by ext y; simp [U]
  have filterJ : X.filter (·∈J)=J := by
    apply Finset.filter_mem_eq_inter.trans
    exact Finset.inter_eq_right.mpr (Finset.sdiff_subset.trans rsub)
  have ss := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_filter,filterU,filterJ] at ss
  rw [integral_finset_sum X (fun y _ => short_integrable sound L m y)]
  simpa only [Finset.sum_const,nsmul_eq_mul,U,J,Finset.card_sdiff_of_subset rsub,
    Finset.card_sdiff_of_subset dsub] using ss

theorem unit_payment (facts : CitedFacts) {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {X : Finset Plane} (L : Layers X) (m : Mode) (on : m ≠ .centresOnly) (B : ℝ)
    (pos : 0<B) (low : B≤unitMean Ω) (ra : 344/1000 ≤ retention Ω (cap Ω a)) (rd : 761/1000 ≤ retention Ω (cap Ω d))
    (hn : 2090≤X.card) (hd : minNonisolatedDegree X 3) :
    let β : ℝ := if m=.r then 1195/10000 else 6195/10000
    B*((unitEdgeCount X:ℝ)-weightedBound X.card (unitEdgeCount X) (X.card-L.R.card : ℕ) (L.R.card-L.D.card : ℕ) (828/1000) β) ≤
      ∫ θ,∑ y∈X,excessCredit L Ω m θ y ∂uniformInterval (2*Real.pi) := by
  intro β
  let U := X\L.R
  let J := L.R\L.D
  have us : U⊆X := Finset.sdiff_subset
  have js : J⊆X := Finset.sdiff_subset.trans L.maximalR.1
  have dis : Disjoint U J := Finset.disjoint_left.mpr fun y hu hj => (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hj).1
  let wgt y : ℝ := ((if y∈eligible L m then 0 else 1)+1-retention Ω (headCap L Ω y))/2
  have each (y) (hy : y∈X) : wgt y ≤ (if y∈U then 828/1000 else 0)+(if y∈J then β else 0) := by
    by_cases root : y∈L.D
    · have zero := retention_zero sound (pos.trans_le low)
      cases m <;> simp [wgt,U,J,β,eligible,headCap,hy,root,L.maximalD.1 root,zero] at *
    by_cases inner : y∈L.R <;> cases m <;>
      simp [wgt,U,J,β,eligible,headCap,hy,root,inner] at * <;> linarith
  let deg (y : Plane) := (unitDegree X y : ℝ)
  have individual (y) (hy : y∈X) :
      ((if y∈eligible L m then 0 else 1 : ℝ)+1-retention Ω (headCap L Ω y))*unitDegree X y/2 ≤
      (if y∈U then (828/1000)*deg y else 0)+(if y∈J then β*deg y else 0) := by
    have mm := mul_le_mul_of_nonneg_right (each y hy) (show 0≤deg y by dsimp [deg]; positivity)
    by_cases u : y∈U <;> by_cases j : y∈J <;> simp only [u,j,ite_true,ite_false,zero_mul,add_mul,wgt,deg] at mm ⊢ <;> linarith
  have sum := Finset.sum_le_sum individual
  have filterT (A : Finset Plane) (sub : A⊆X) : X.filter (·∈A)=A := by ext y; simp; exact fun hy => sub hy
  rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_filter,filterT U us,filterT J js,← Finset.mul_sum,← Finset.mul_sum] at sum
  have bound := weighted_degree_upper facts X U J (828/1000) β hn hd us js dis (by norm_num) (by dsimp [β]; split <;> norm_num)
  rw [show U.card=X.card-L.R.card from Finset.card_sdiff_of_subset L.maximalR.1,
    show J.card=L.R.card-L.D.card from Finset.card_sdiff_of_subset L.maximalD.1] at bound
  have charge := sum.trans bound
  have h := expected_unit_credit W Ω sound X L m
  apply le_trans _ h
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left charge _) pos.le).trans
    ((mul_le_mul_of_nonneg_left (le_max_right ..) pos.le).trans
      (mul_le_mul_of_nonneg_right low (le_max_left ..)))

end
end HadwigerNelson.Forest
