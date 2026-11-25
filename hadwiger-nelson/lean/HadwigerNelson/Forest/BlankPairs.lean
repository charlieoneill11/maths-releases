import HadwigerNelson.Forest.Credits
import HadwigerNelson.Forest.Potential
import HadwigerNelson.Placement.Edge

namespace HadwigerNelson.Forest
open MeasureTheory Set Placement Centres
noncomputable section
attribute [local instance] Classical.propDecidable

def pairBlanks (W : Wave.Datum) (θ : ℝ) (x y : Plane) : Set Translation :=
  {t | colour W (θ,t) x=none ∧ colour W (θ,t) y=none}

theorem pairBlanks_measurable (W : Wave.Datum) (θ : ℝ) (x y : Plane) :
    MeasurableSet (pairBlanks W θ x y) := by
  have m (v : Plane) : MeasurableSet {t : Translation | colour W (θ,t) v=none} := by
    apply (Wave.blank_closed W).measurableSet.preimage (f:=fun t => rotate θ v + translationPoint t)
    fun_prop
  exact (m x).inter (m y)

theorem pairBlanks_probability (W : Wave.Datum) (θ : ℝ) (x y : Plane) :
    (translationLaw W).real (pairBlanks W θ x y) = Wave.bothBlank W (rotate θ (y-x)) := by
  let v := rotate θ (y-x)
  let A := {z : Plane | Wave.colour W z=none ∧ Wave.colour W (z+v)=none}
  let S := rotate θ x
  have hm : MeasurableSet A := (Wave.blank_closed W).measurableSet.inter
    ((Wave.blank_closed W).measurableSet.preimage (continuous_id.add continuous_const).measurable)
  have per (z p : Plane) (hp : p∈Wave.lattice W) :
      A.indicator (1 : Plane → ℝ) (z+p)=A.indicator 1 z := by
    have e : (z+p)+v=(z+v)+p := by abel
    simp [A,indicator, e,Wave.colour_periodic W _ _ hp]
  have pointSet : pairBlanks W θ x y = (fun t => S+translationPoint t) ⁻¹' A := by
    ext t
    have eq : (S+translationPoint t)+v=place (θ,t) y := by
      dsimp [S,v,place,translationPoint]; rw [rotate_sub]; abel
    simp only [pairBlanks,A,mem_preimage,mem_setOf_eq,eq]
    rfl
  have int {f : Translation → Plane} (hf : Measurable f) : Integrable (fun t => A.indicator (1 : Plane → ℝ) (f t)) (translationLaw W) := by
    simpa only [Set.indicator,Set.mem_preimage] using
      (integrable_const (μ:=translationLaw W) (1 : ℝ)).indicator (hm.preimage hf)
  have avg := translation_average_invariant W (A.indicator 1) S per (int continuous_translationPoint.measurable)
    (int (continuous_const.add continuous_translationPoint).measurable)
  have rest (f : Translation → Plane) (hf : Measurable f) :
      (∫ t,A.indicator (1 : Plane → ℝ) (f t) ∂translationLaw W)=(translationLaw W).real (f ⁻¹' A) := by
    rw [← integral_indicator_one (μ:=translationLaw W) (hm.preimage hf)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by by_cases ht : f t∈A <;> simp [ht]
  rw [pointSet]
  exact ((rest (fun t => S+translationPoint t) (continuous_const.add continuous_translationPoint).measurable).symm.trans avg).trans (rest _ continuous_translationPoint.measurable)

theorem nonneg_omega {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0≤y) : 0 ≤ Ω x y :=
  (sound x y 0 (by simpa using hx) (by simpa using hy)).1

theorem unitStep_nonneg {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω) (k : ℕ) :
    0 ≤ unitStep Ω k := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih =>
    apply le_min ih
    apply nonneg_omega sound
    · unfold unitBin w; positivity
    · positivity

theorem short_nonneg {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {ρ : ℝ} (hρ : 0≤ρ) {i : ℕ} (hi : i≤8191) : 0≤ lowerShort Ω ρ i := by
  have b : shortBin i ≤ 1 := by unfold shortBin; have := (show (i:ℝ)≤8191 by exact_mod_cast hi); linarith
  have a : 0≤shortBin i := by unfold shortBin; positivity
  have sq := pow_le_pow_left₀ a b 2
  unfold lowerShort
  apply nonneg_omega sound
  · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  · unfold shortBin; positivity

theorem cap_nonneg {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {ρ : ℝ} (hρ : 0≤ρ) : 0≤cap Ω ρ := by
  have := le_csSup (Finite.bddAbove_range (fun i : Fin 8192 => lowerShort Ω ρ i))
    (Set.mem_range_self (0 : Fin 8192))
  apply mul_nonneg _ ((short_nonneg sound hρ (i:=0) (by decide)).trans this)
  split <;> norm_num

theorem edgeShort_bounds {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    {X : Finset Plane} (L : Layers X) (m : Mode) (θ : ℝ) (y : Plane) :
    0 ≤ edgeShort L Ω m θ y ∧ edgeShort L Ω m θ y ≤ headCap L Ω y := by
  have ha : 0≤a := by norm_num [a,δR]
  have hd : 0≤d := by norm_num [d,δ]
  have capρ (ρ : ℝ) (hρ : 0≤ρ) (v : Plane) :
      0 ≤ cappedShort Ω ρ (shortIndex v) ∧ cappedShort Ω ρ (shortIndex v) ≤ cap Ω ρ :=
    ⟨le_min (short_nonneg sound hρ (min_le_left ..)) (cap_nonneg sound hρ),min_le_right ..⟩
  by_cases yd : y∈L.D
  · simp [edgeShort,headCap,yd]
  by_cases centre : m=.centresOnly
  · by_cases yr : y∈L.R <;> simp [edgeShort,headCap,yd,centre,yr,cap_nonneg sound ha,cap_nonneg sound hd]
  · by_cases yr : y∈L.R
    · simpa [edgeShort,headCap,centre,yd,yr] using capρ d hd (rotate θ (y-L.parent y))
    · simpa [edgeShort,headCap,centre,yd,yr] using capρ a ha (rotate θ (y-L.parent y))

theorem parent_edge {X : Finset Plane} (L : Layers X) {y : Plane} (hy : y∈X) (hd : y∉L.D) :
    L.parent y ∈ X ∧ y ≠ L.parent y ∧ dist y (L.parent y) ≤ 2*(if y∈L.R then d else a) := by
  classical
  by_cases hr : y∈L.R
  · obtain ⟨hp,hb⟩ := L.inner y hr hd
    exact ⟨L.maximalR.1 (L.maximalD.1 hp),fun e => hd (e ▸ hp),by rw [if_pos hr,d,show 2*(δ/2)=δ by ring]; exact hb⟩
  · obtain ⟨hp,hb⟩ := L.outer y hy hr
    exact ⟨L.maximalR.1 hp,fun e => hr (e ▸ hp),by rw [if_neg hr,a,show 2*(δR/2)=δR by ring]; exact hb⟩

theorem edgeUnit_nonneg {W : Wave.Datum} {Ω : ℝ → ℝ → ℝ} (sound : Wave.holeEnclosure W Ω)
    (θ : ℝ) (x y : Plane) : 0 ≤ edgeUnit Ω θ x y := by
  unfold edgeUnit
  split
  · exact unitStep_nonneg sound _
  · rfl

end
end HadwigerNelson.Forest
