import HadwigerNelson.Forest.Selection
import HadwigerNelson.Placement.Edge

namespace HadwigerNelson.Forest
open Placement MeasureTheory Set Centres Crossings
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def headEvent {X : Finset Plane} (W : Wave.Datum) (L : Layers X) (m : Mode) (p : Profile)
    (y : Plane) : Set Sample :=
  {ω | ∃ x∈X,allCandidates L m p ω.1 x y ∧ colour W ω x=none ∧ colour W ω y=none}

theorem unitCandidate_measurable (x y : Plane) : MeasurableSet {θ | unitCandidate θ x y} := by
  let K := (fun t => Wave.point (Real.sin t) (Real.cos t)) '' Icc (-w) w
  have compact : IsCompact K := isCompact_Icc.image (continuous_point Real.continuous_sin Real.continuous_cos)
  have eq : {θ | unitCandidate θ x y}=(fun θ => rotate θ (y-x)) ⁻¹' K := by
    ext θ
    simp only [unitCandidate,K,mem_preimage,mem_image,mem_Icc,mem_setOf_eq,abs_le]
    exact exists_congr fun t => and_congr_right fun _ => eq_comm
  rw [eq]; exact compact.isClosed.measurableSet.preimage (by unfold rotate; fun_prop)

theorem headEvent_measurable {X : Finset Plane} (W : Wave.Datum) (L : Layers X) (m : Mode) (p : Profile)
    (cm : ∀ x y,MeasurableSet {θ | candidate X L.D p θ x y}) (y : Plane) :
    MeasurableSet (headEvent W L m p y) := by
  have blank (x : Plane) : MeasurableSet {ω : Sample | colour W ω x=none} :=
    (Wave.blank_closed W).measurableSet.preimage (continuous_place x).measurable
  have active (x : Plane) : MeasurableSet {θ | allCandidates L m p θ x y} := by
    have ordinaryM : MeasurableSet {θ | ordinary L m θ x y} := by
      by_cases e : m=.centresOnly
      · simp [ordinary,e]
      by_cases short : y∉L.D ∧ L.parent y=x
      · simp [ordinary,e,short]
      by_cases eligible' : x∈eligible L m
      · simpa [ordinary,e,short,eligible'] using unitCandidate_measurable x y
      · simp [ordinary,e,short,eligible']
    exact ordinaryM.union (cm x y)
  let E (x : Plane) := {ω : Sample | allCandidates L m p ω.1 x y ∧ colour W ω x=none ∧ colour W ω y=none}
  have eq : headEvent W L m p y = ⋃ x∈X,E x := by
    ext ω; simp only [headEvent,E,mem_setOf_eq,mem_iUnion]; constructor <;> rintro ⟨x,hx,h⟩ <;> exact ⟨x,hx,h⟩
  rw [eq]
  exact X.measurableSet_biUnion fun x _ => ((active x).preimage measurable_fst).inter ((blank x).inter (blank y))

private def incident {α V : Type*} (X : Finset V) (A : V → Set α) (ω : α) : Finset V :=
  X.filter fun v => ω∈A v

private theorem mem_incident {α V : Type*} {X : Finset V} {A : V → Set α} {ω : α} {y : V} :
    y∈incident X A ω ↔ y∈X ∧ ω∈A y := Finset.mem_filter

/-- Integrating the cardinality of a finite collection of physical events. -/
theorem event_count {α V : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : Finset V) (A : V → Set α) (meas : ∀ v∈X,MeasurableSet (A v)) :
    let h := fun ω => ((incident X A ω).card : ℝ)
    Integrable h μ ∧ (∫ ω,h ω ∂μ)=∑ v∈X,μ.real (A v) := by
  intro h
  let f (v : V) := (A v).indicator (1 : α → ℝ)
  have eq : h=fun ω => ∑ v∈X,f v ω := by
    funext ω
    simp only [h,incident,Finset.natCast_card_filter,f,Set.indicator_apply,Pi.one_apply]
  have hi (v) (hv : v∈X) : Integrable (f v) μ := (integrable_const 1).indicator (meas v hv)
  rw [eq,integral_finset_sum X hi]
  exact ⟨integrable_finset_sum X hi,Finset.sum_congr rfl (fun v hv => integral_indicator_one (meas v hv))⟩

/-- Placement-wise selection, averaging the number of blanks and all heads,
and subtracting the locked-star gain over both ends of every unit edge. -/
theorem score_from_heads (W : Wave.Datum) (X : Finset Plane) (L : Layers X) (m : Mode) (p : Profile)
    (cm : ∀ x y,MeasurableSet {θ | candidate X L.D p θ x y})
    (bad : ¬ ∃ c : Plane → Fin 6,∀ x∈X,∀ y∈X,dist x y=1 → c x ≠ c y)
    (β : ℝ) (stars : ∀ E : Finset (Plane×Plane), (∀ e∈E,dist e.1 e.2=1) → ∀ v,
      β*Stars.degree E v≤∫ ω, Stars.gain E (Proof.placedColours W ω) v ∂law W) :
    1 + (∑ y∈X,(law W).real (headEvent W L m p y)) ≤
      X.card*blankDensity W + unitEdgeCount X*(meanMonoProb W-β/2) := by
  classical
  obtain ⟨E,card,he,cov⟩ := unit_representatives X
  have unit (e) (h : e∈E) := (he e h).2.2
  have ends (e) (h : e∈E) := And.intro (he e h).1 (he e h).2.1
  have loops (e) (h : e∈E) : e.1≠e.2 := by intro eq; have := unit e h; simp [eq] at this
  have impossible : ¬∃ c : Plane → Fin 6,∀ e∈E,c e.1≠c e.2 := by
    rintro ⟨c,hc⟩
    apply bad; refine ⟨c,fun x hx y hy hu => ?_⟩
    rcases cov x hx y hy hu with h|h
    · exact hc _ h
    · exact (hc _ h).symm
  let B := incident X (fun v => {s : Sample | colour W s v=none})
  let T := incident X (headEvent W L m p)
  have sub (ω) : T ω⊆B ω := by
    intro v hv; obtain ⟨hv,_,_,_,_,none⟩ := mem_incident.mp hv
    exact mem_incident.mpr ⟨hv,none⟩
  have component (ω : Sample) (hb : ∃ v∈X,Proof.placedColours W ω v = none) : 1≤(B ω).card-(T ω).card := by
    obtain ⟨v,hv,blank⟩ := hb
    have nonempty : (B ω).Nonempty := ⟨v,mem_incident.mpr ⟨hv,by simpa [Proof.placedColours] using blank⟩⟩
    let rel := allCandidates L m p ω.1
    obtain ⟨F,size,_,_,lt⟩ := select_incoming (B ω) rel (rootHeight L ω.1) (depth L)
      (fun x hx y hy h => candidate_increases L m p ω.1 (mem_incident.mp hx).1 (mem_incident.mp hy).1 h)
    have eq : (B ω).filter (fun y => ∃ x∈B ω, rel x y) = T ω := by
      ext y
      constructor
      · intro hy
        obtain ⟨yb,x,xb,yes⟩ := Finset.mem_filter.mp hy
        obtain ⟨yx,y0⟩ := mem_incident.mp yb
        obtain ⟨xx,x0⟩ := mem_incident.mp xb
        exact mem_incident.mpr ⟨yx,x,xx,yes,x0,y0⟩
      · intro hy
        obtain ⟨yx,x,xx,yes,x0,y0⟩ := mem_incident.mp hy
        exact Finset.mem_filter.mpr ⟨mem_incident.mpr ⟨yx,y0⟩,x,mem_incident.mpr ⟨xx,x0⟩,yes⟩
    rw [eq] at size
    have := lt nonempty
    omega
  have mh (y : Plane) := headEvent_measurable W L m p cm y
  have mb (x : Plane) : MeasurableSet {ω : Sample | colour W ω x=none} :=
    (Wave.blank_closed W).measurableSet.preimage (continuous_place x).measurable
  have ⟨Bi,Bmean⟩ := event_count (μ:=law W) X _ (fun v _ => mb v)
  have ⟨Ti,Tmean⟩ := event_count (μ:=law W) X _ (fun v _ => mh v)
  have beq (v : Plane) : (law W).real {ω : Sample | colour W ω v=none}=blankDensity W := by
    rw [← integral_indicator_one (mb v)]
    simpa only [Set.indicator_apply,mem_setOf_eq,Pi.one_apply] using placed_blank_expectation W v
  simp_rw [beq] at Bmean
  simp only [Finset.sum_const,nsmul_eq_mul] at Bmean
  change Integrable (fun ω => ((B ω).card:ℝ)) (law W) at Bi
  change Integrable (fun ω => ((T ω).card:ℝ)) (law W) at Ti
  change (∫ ω,((B ω).card:ℝ) ∂law W)=_ at Bmean
  change (∫ ω,((T ω).card:ℝ) ∂law W)=_ at Tmean
  have ceq (ω : Sample) : (((B ω).card-(T ω).card : ℕ):ℝ)=(B ω).card-((T ω).card:ℝ) :=
    Nat.cast_sub (Finset.card_le_card (sub ω))
  have Yi : Integrable (fun ω => (((B ω).card-(T ω).card : ℕ):ℝ)) (law W) := by
    simp_rw [ceq]; exact Bi.sub Ti
  have ei (e : Plane×Plane) : Integrable (fun ω => Stars.badIndicator (Proof.placedColours W ω) e) (law W) := by
    simp_rw [Proof.badIndicator_eq]
    exact integrable_sameColour W (continuous_place e.1).measurable (continuous_place e.2).measurable
  have Xi : Integrable (fun ω => (Stars.badCount E (Proof.placedColours W ω):ℝ)) (law W) := by
    simp_rw [Stars.sum_badIndicator]; exact integrable_finset_sum E (fun e _ => ei e)
  have gi (v) (hv:v∈X) := Stars.integrable_gain (μ:=law W) X E v hv ends (Proof.placedColours W) (fun x _ => Proof.measurable_placedColour W x)
  have key := Stars.one_bad_edge_expectation X E (Proof.placedColours W)
    (fun ω => (B ω).card-(T ω).card) ends loops (Filter.Eventually.of_forall component) impossible Yi Xi gi
  simp_rw [ceq,Stars.sum_badIndicator] at key
  rw [integral_sub Bi Ti,Bmean,Tmean,integral_finset_sum E (fun e _ => ei e)] at key
  have BadMean : (∑ e∈E,∫ ω,Stars.badIndicator (Proof.placedColours W ω) e ∂law W) =
      E.card*meanMonoProb W := by
    calc _ = ∑ _∈E,meanMonoProb W := Finset.sum_congr rfl (fun e he => Proof.unit_edge_mean W e (unit e he))
         _ = _ := by simp
  have total := Finset.sum_le_sum (fun v (_ : v∈X) => stars E unit v)
  have deg : ∑ v∈X,(Stars.degree E v:ℝ) = 2*E.card := by exact_mod_cast Stars.sum_degree X E ends
  rw [← Finset.mul_sum,deg,card] at total
  rw [BadMean,card] at key
  linarith

end
end HadwigerNelson.Forest
