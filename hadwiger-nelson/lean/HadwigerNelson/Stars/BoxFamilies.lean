import HadwigerNelson.Stars.CellScore
import HadwigerNelson.Stars.SourceArea
import HadwigerNelson.Stars.AllDegrees
import HadwigerNelson.Stars.RealFourier

namespace HadwigerNelson.Stars.BoxCheck
open MeasureTheory
open scoped BigOperators ComplexConjugate
noncomputable section

private abbrev Family := (Fin 14464) ⊕ (Fin 252)
private def rect : Family → Source := Sum.elim (fun i => source i.val) (fun j => saturated j.val)
private def active (harm nat : Bool) : Family → Bool
  | .inl i => harm && (!nat || (source i.val).separate)
  | .inr _ => nat

private def ratio {d : Nat} (k : Fin harmonics) (φ : Fin d → ℝ) := powerRatio (fun j => anglePhase (φ j)) k

def harmonicLocal {d : Nat} (k : Fin harmonics) (φ : Fin d → ℝ) (i : Fin 14464) :=
  let r := moments arcTable (source i.val)
  max 0 (meanValue r + magnitudeValue k.val r * ratio k φ)

def saturatedLocal (d : Nat) (j : Fin 252) :=
  max 0 ((nativeFraction arcTable (saturated j.val) : ℝ)/quant-1/(d:ℝ))

private def cellCredit {d : Nat} (k : Fin harmonics) (φ : Fin d → ℝ) : Family → ℝ
  | .inl i => harmonicLocal k φ i
  | .inr j => 2*saturatedLocal d j

private theorem pairwise {harm nat : Bool} (pass : checkSourceBoxes = true) {i j : Family}
    (si : active harm nat i = true) (sj : active harm nat j = true) {z : Plane}
    (a : z∈physicalSource (rect i)) (b : z∈physicalSource (rect j)) : i=j := by
  have valid := (checkSourceBoxes_spec pass).1
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      apply congrArg Sum.inl; apply Fin.ext; by_contra ne
      exact checked_disjoint (valid i) (valid j) ne a b
    | inr j =>
      change nat=true at sj
      have sep : (source i.val).separate=true := by simpa [active,sj] using (Bool.and_eq_true_iff.mp si).2
      exact (harmonic_separate_saturated sep j a b).elim
  | inr i =>
    cases j with
    | inl j =>
      change nat=true at si
      have sep : (source j.val).separate=true := by simpa [active,si] using (Bool.and_eq_true_iff.mp sj).2
      exact (harmonic_separate_saturated sep i b a).elim
    | inr j =>
      apply congrArg Sum.inr; by_contra ne
      exact saturated_disjoint i j ne a b

private theorem array_sums {α : Type*} {n : Nat} (f : Fin n → α) (g : α → ℝ) :
    ∑ i : Fin (Array.ofFn f).size, g ((Array.ofFn f)[i.val]) = ∑ i, g (f i) := by
  apply Fintype.sum_equiv (finCongr Array.size_ofFn) _ _
  intro i
  rw [Array.getElem_ofFn]
  rfl

private theorem harmonic_separate (s : Source) : (moments arcTable s).separate = s.separate := rfl
private theorem harmonic_area (s : Source) : (moments arcTable s).area = s.area := rfl

private def weight (s : Source) := 2*(s.area:ℝ)/CompleteWave.xInt

private theorem harmonic_sum (q : Nat) (k : Fin harmonics) {d : Nat} (φ : Fin d → ℝ) :
    (∑ i : Fin (rowRange arcTable 0 14464).size,
      let r := (rowRange arcTable 0 14464)[i.val]
      areaWeight q r * max 0 (meanValue r + magnitudeValue k.val r * ratio k φ)) =
    ∑ i : Fin 14464, if q == 23 || (source i.val).separate then weight (source i.val) * harmonicLocal k φ i else 0 := by
  let g (r : Row) := areaWeight q r * max 0 (meanValue r + magnitudeValue k.val r * ratio k φ)
  change (∑ i : Fin (rowRange arcTable 0 14464).size, g ((rowRange arcTable 0 14464)[i.val])) = _
  unfold rowRange
  rw [array_sums]
  apply Finset.sum_congr rfl
  intro i _
  simp only [g,zero_add,areaWeight,harmonic_separate,harmonic_area,harmonicLocal,weight]
  split <;> simp_all

private theorem native_sum (d : Nat) (pos : 0<d) :
    nativeValue d (nativeNumerator (saturatedData arcTable) d) =
      ∑ i : Fin 252, weight (saturated i.val) * (2*saturatedLocal d i) := by
  rw [nativeValue_eq _ _ pos]
  let g (p : Int × Int) := (4*(p.1:ℝ)/CompleteWave.xInt)*max 0 ((p.2:ℝ)/quant-1/d)
  change (∑ i : Fin (saturatedData arcTable).size, g ((saturatedData arcTable)[i.val])) = _
  unfold saturatedData
  rw [array_sums]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [g,weight,saturatedLocal]; ring

attribute [local irreducible] rowRange arcTable moments source saturated saturatedData nativeNumerator

private theorem family_sum (harm nat : Bool) (pass : checkSourceBoxes = true) {d : Nat} (hd : 0<d)
    (k : Fin harmonics) (φ : Fin d → ℝ)
    (harmBounds : harm=true → ∀ (ψ : Fin d → ℝ) (i : Fin 14464) z, z∈physicalSource (source i.val) →
      (d:ℝ)/2*harmonicLocal k ψ i ≤ angularGain Wave.completeDatum ψ z)
    (natBounds : nat=true → ∀ (ψ : Fin d → ℝ) (j : Fin 252) z, z∈physicalSource (saturated j.val) →
      (d:ℝ)*saturatedLocal d j ≤ angularGain Wave.completeDatum ψ z) :
    (∑ i : Fin 14464, if harm && (!nat || (source i.val).separate) then weight (source i.val)*harmonicLocal k φ i else 0)
    + (if nat then ∑ i : Fin 252, weight (saturated i.val)*(2*saturatedLocal d i) else 0) ≤ cellScore Wave.completeDatum φ := by
  classical
  let S := Finset.univ.filter (fun e : Family => active harm nat e)
  have sel {e : Family} (h : e∈S) : active harm nat e=true := (Finset.mem_filter.mp h).2
  have valid := checkSourceBoxes_spec pass
  have lower := normalized_cell_box_sum Wave.completeDatum hd φ S (fun e => physicalSource (rect e)) (cellCredit k)
    (fun e _ => (physicalSource_open _).measurableSet)
    (fun e _ => by cases e with | inl i => exact physical_source_half i (valid.1 i) | inr j => exact physical_saturated_half j (valid.2 j))
    (fun _ hi _ hj _ => pairwise pass (sel hi) (sel hj))
    (fun e _ b h => by
      cases e with
      | inr j => rfl
      | inl i =>
        unfold cellCredit harmonicLocal ratio powerRatio
        rw [norm_anglePhase_signAngle])
    (fun ψ e he z hz => by
      cases e with
      | inl i => exact harmBounds (Bool.and_eq_true_iff.mp (sel he)).1 ψ i z hz
      | inr j =>
        have h := natBounds (sel he) ψ j z hz
        change (d:ℝ)/2*(2*saturatedLocal d j) ≤ _
        linarith)
  have area (e : Family) : volume.real (physicalSource (rect e))/(Wave.completeDatum.x*Wave.H) = weight (rect e) := by
    apply physical_fourier_weight
    · cases e with
      | inl i => exact (sourceValid_spec (valid.1 i)).1.le
      | inr j => change (saturated j.val).xlo≤(saturated j.val).xhi; simp [saturated]
    · cases e with
      | inl i => exact (sourceValid_spec (valid.1 i)).2.1.le
      | inr j => change (saturated j.val).ylo≤(saturated j.val).yhi; simp [saturated]
  simp_rw [area] at lower
  simp only [S,Finset.sum_filter,Fintype.sum_sum_type,active,rect,cellCredit,Sum.elim_inl,Sum.elim_inr] at lower
  cases nat <;> simpa only [Bool.not_false,Bool.not_true,Bool.true_or,Bool.false_or,Bool.and_true,Bool.false_eq_true,if_false,if_true,Finset.sum_const_zero,add_zero] using lower

private theorem credit_split {d : Nat} (k : Fin harmonics) (φ : Fin d → ℝ) :
    selectedCredit (rowRange arcTable 0 14464) (saturatedData arcTable) d k (powerRatio (fun j => anglePhase (φ j)) k) =
      let q := max 23 d
      nativeValue q (if q==23 then 0 else nativeNumerator (saturatedData arcTable) q) +
      ∑ i : Fin 14464, if q==23 || (source i.val).separate then weight (source i.val)*harmonicLocal k φ i else 0 :=
  congrArg (fun t => nativeValue (max 23 d) (if max 23 d==23 then 0 else nativeNumerator (saturatedData arcTable) ((max 23 d : Nat):Int))+t)
    (harmonic_sum (max 23 d) k φ)

/-- The degree-dependent choice of active source rectangles contributes the
selected Fourier credit, with native rectangles included only above degree 23. -/
theorem selected_cell_bound (pass : checkSourceBoxes = true) {d : Nat} (hd : 0<d)
    (k : Fin harmonics) (φ : Fin d → ℝ)
    (harmBounds : ∀ (ψ : Fin d → ℝ) (i : Fin 14464) z, z∈physicalSource (source i.val) →
      (d:ℝ)/2*harmonicLocal k ψ i ≤ angularGain Wave.completeDatum ψ z)
    (natBounds : 23<d → ∀ (ψ : Fin d → ℝ) (j : Fin 252) z, z∈physicalSource (saturated j.val) →
      (d:ℝ)*saturatedLocal d j ≤ angularGain Wave.completeDatum ψ z) :
    selectedCredit (rowRange arcTable 0 14464) (saturatedData arcTable) d k (powerRatio (fun j => anglePhase (φ j)) k) ≤ cellScore Wave.completeDatum φ := by
  rw [credit_split k φ]
  by_cases small : d≤23
  · have f := family_sum true false pass hd k φ (fun _ => harmBounds) (by simp)
    have zero : nativeValue 23 0 = 0 := by simp [nativeValue]
    simpa only [max_eq_left small,beq_self_eq_true,if_true,Bool.not_false,Bool.true_or,Bool.true_and,
      Bool.false_eq_true,if_false,zero,add_zero,zero_add] using f
  · have larger : 23<d := by omega
    have f := family_sum true true pass hd k φ (fun _ => harmBounds) (fun _ => natBounds larger)
    have ne : (d==23)=false := by simp [show d≠23 by omega]
    simpa only [max_eq_right larger.le,ne,Bool.false_eq_true,if_false,Bool.false_or,native_sum d hd,
      Bool.true_and,Bool.not_true,if_true,add_comm] using f

/-- Using the 252 saturated native boxes alone gives the high-degree bound. -/
theorem saturated_cell_bound (pass : checkSourceBoxes = true) {d : Nat} (hd : 0<d)
    (φ : Fin d → ℝ)
    (natBounds : ∀ (ψ : Fin d → ℝ) (j : Fin 252) z, z∈physicalSource (saturated j.val) →
      (d:ℝ)*saturatedLocal d j ≤ angularGain Wave.completeDatum ψ z) :
    nativeValue d (nativeNumerator (saturatedData arcTable) d) ≤ cellScore Wave.completeDatum φ := by
  rw [native_sum _ hd]
  have f := family_sum false true pass hd (⟨0,by decide⟩ : Fin harmonics) φ (by simp) (fun _ => natBounds)
  simpa using f

private theorem array_forall {n : Nat} {α : Type*} (f : Fin n → α) (P : α → Prop)
    (h : ∀ j, P (f j)) (i : Fin (Array.ofFn f).size) : P ((Array.ofFn f)[i.val]) := by
  rw [Array.getElem_ofFn]
  exact h _

private theorem nonneg_amplitude (table : Array Arc) (s : Source) (k : Fin harmonics) :
    0 ≤ magnitudeValue k.val (moments table s) := by
  have h : 0 ≤ (moments table s).magnitude[k.val]?.getD 0 := by
    simp only [moments,momentsFrom,Array.getElem?_ofFn,k.isLt,dif_pos,Option.getD_some]
    exact le_max_left _ _
  exact div_nonneg (by exact_mod_cast h) (by norm_num [quant])

/-- Combining the area, degree and Fejér checks gives the lower bound on
angular gain per incidence in the complete wave. -/
theorem cellScore_eight (pass : checkSourceBoxes = true)
    (credit : checkData (rowRange arcTable 0 14464) (saturatedData arcTable) = true)
    {d : Nat} (hd : 0<d) (φ : Fin d → ℝ)
    (harmBounds : d≤27 → ∀ (k : Fin harmonics) (ψ : Fin d → ℝ) (i : Fin 14464) z,
      z∈physicalSource (source i.val) → (d:ℝ)/2*harmonicLocal k ψ i ≤ angularGain Wave.completeDatum ψ z)
    (natBounds : 23<d → ∀ (ψ : Fin d → ℝ) (j : Fin 252) z, z∈physicalSource (saturated j.val) →
      (d:ℝ)*saturatedLocal d j ≤ angularGain Wave.completeDatum ψ z) :
    (8:ℝ)/10^9 ≤ cellScore Wave.completeDatum φ := by
  apply all_degrees_sound _ _ _ hd (fun j => anglePhase (φ j)) (fun j => norm_anglePhase _) _ _ _ _ _ _ credit
  · unfold rowRange
    exact array_forall _ (fun r : Row => 0 ≤ r.area) (fun j => by
      change 0 ≤ (moments arcTable (source (0+j.val))).area
      rw [Nat.zero_add,harmonic_area]
      have spec := sourceValid_spec ((checkSourceBoxes_spec pass).1 j)
      exact mul_nonneg (sub_nonneg.mpr spec.1.le) (sub_nonneg.mpr spec.2.1.le))
  · intro k
    unfold rowRange
    exact array_forall _ (fun r : Row => 0 ≤ magnitudeValue k.val r) (fun j => nonneg_amplitude _ _ k)
  · unfold saturatedData
    exact array_forall _ (fun p : Int × Int => 0 ≤ p.1) (fun j => by
      change 0 ≤ (saturated j.val).area
      simp [Source.area,saturated])
  · intro small k
    exact selected_cell_bound pass hd k φ (harmBounds small k) natBounds
  · intro big
    exact saturated_cell_bound pass hd φ (natBounds (by omega))

end
end HadwigerNelson.Stars.BoxCheck
