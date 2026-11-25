import HadwigerNelson.Wave.Holes.Monotone
import HadwigerNelson.Wave.Geometry.Blank
import HadwigerNelson.Stars.BoxIntegral
import HadwigerNelson.Placement.CellMeasure

namespace HadwigerNelson.Wave
open MeasureTheory Set
open scoped ENNReal Pointwise
noncomputable section

private def shift (r : Fin 3) : Plane := point 0 (↑r.val*H)

private theorem lattice_shift (W : Datum) (i j : ℤ) (r : Fin 3) :
    latticePoint W i j + shift r = holeLatticePoint W i (3*j+r.val) := by
  ext k
  fin_cases k <;> simp [shift,latticePoint,holeLatticePoint] <;> ring

private theorem holeLattice_blank (W : Datum) {z a : Plane} (ha : a∈holeLattice W)
    (hz : z∈hole W) : colour W (a+z) = none := by
  obtain ⟨i,j,rfl⟩ := (mem_holeLattice ..).mp ha
  apply holeCopies_subset_blank W
  exact ⟨i,j,by simpa only [add_sub_cancel_left] using hz⟩

private theorem same_copy {W : Datum} {r t : Fin 3} {g h : lattice W}
    {u w : Plane} (hu : u∈hole W) (hw : w∈hole W)
    (e : (g:Plane)+(shift r+u) = (h:Plane)+(shift t+w)) : r=t ∧ g=h := by
  obtain ⟨i,j,eg⟩ := (mem_lattice W g).mp g.2
  obtain ⟨k,l,eh⟩ := (mem_lattice W h).mp h.2
  let z : Plane := ↑g+(shift r+u)
  have hz : z-holeLatticePoint W i (3*j+r.val) ∈ hole W := by
    rw [←lattice_shift,←eg]
    simpa [z,←add_assoc] using hu
  have hz' : z-holeLatticePoint W k (3*l+t.val) ∈ hole W := by
    rw [←lattice_shift,←eh,show z= ↑h+(shift t+w) from e]
    simpa [←add_assoc] using hw
  obtain ⟨ik,jl⟩ := holeCopies_disjoint hz hz'
  have re : r.val=t.val := by omega
  have je : j=l := by omega
  exact ⟨Fin.ext re,Subtype.ext (eg.trans (ik ▸ je ▸ eh.symm))⟩

/-- All three translates modulo the coloured lattice contribute their full
area to its fundamental rectangle. -/
private theorem three_copies (W : Datum) (v δ : Plane) (hδ : δ ∈ holeLattice W) :
    let A := holeOverlap W (-(v-δ))
    let E := {z : Plane | colour W z = none ∧ colour W (z+v) = none}
    (3:ℝ≥0∞)*volume A ≤ volume (E ∩ cell W (3*H)) := by
  classical
  dsimp only
  let A := holeOverlap W (-(v-δ))
  let C := cell W (3*H)
  let B (r : Fin 3) : Set Plane := shift r +ᵥ A
  let family (r : Fin 3) : Set Plane := (⋃ g : lattice W, g +ᵥ B r) ∩ C
  have mA : MeasurableSet A := measurable_holeOverlap W _
  have mB (r : Fin 3) : MeasurableSet (B r) := mA.const_vadd _
  have mC : MeasurableSet C := cell_measurable W _
  have mf (r : Fin 3) : MeasurableSet (family r) :=
    (MeasurableSet.iUnion (fun g : lattice W => (mB r).const_vadd g)).inter mC
  have unique {r t : Fin 3} {g h : lattice W} {z : Plane}
      (a : z ∈ g +ᵥ B r) (b : z ∈ h +ᵥ B t) : r=t ∧ g=h := by
    obtain ⟨_,⟨u,hu,rfl⟩,rfl⟩ := a
    obtain ⟨_,⟨w,hw,rfl⟩,e⟩ := b
    exact same_copy hu.1 hw.1 e.symm
  have ma (r : Fin 3) : volume (family r) = volume A := by
    have dis : Pairwise fun g h : lattice W => Disjoint (g +ᵥ B r) (h +ᵥ B r) :=
      fun _ _ ne => Set.disjoint_left.mpr fun _ a b => ne (unique a b).2
    change volume ((⋃ g : lattice W, g +ᵥ B r)∩C)=volume A
    rw [Stars.periodised_measure (lattice_fundamental W) mC (mB r) dis]
    exact measure_vadd volume (shift r) A
  have dis : Pairwise fun r t : Fin 3 => Disjoint (family r) (family t) := by
    intro r t ne
    apply Set.disjoint_left.mpr
    intro z a b
    obtain ⟨g,hg⟩ := mem_iUnion.mp a.1
    obtain ⟨h,hh⟩ := mem_iUnion.mp b.1
    exact ne (unique hg hh).1
  have mfam : volume (⋃ r, family r) = 3*volume A := by
    rw [measure_iUnion dis mf,tsum_fintype,Fin.sum_univ_three,ma,ma,ma]
    ring
  rw [←mfam]
  apply measure_mono
  intro z hz
  obtain ⟨r,hz⟩ := mem_iUnion.mp hz
  obtain ⟨g,hg⟩ := mem_iUnion.mp hz.1
  refine ⟨?_,hz.2⟩
  obtain ⟨_,⟨u,hu,rfl⟩,rfl⟩ := hg
  have gmem : (g:Plane)+shift r ∈ holeLattice W := by
    obtain ⟨i,j,eg⟩ := (mem_lattice W g).mp g.2
    exact (mem_holeLattice W _).mpr ⟨_,_,eg ▸ lattice_shift W i j r⟩
  have first := holeLattice_blank W gmem hu.1
  have second := holeLattice_blank W ((holeLattice W).add_mem gmem hδ) hu.2
  change colour W (↑g+(shift r+u))=none ∧ colour W (↑g+(shift r+u)+v)=none
  exact ⟨by simpa only [add_assoc] using first,by convert second using 2 <;> abel⟩

private theorem bothBlank_lower (W : Datum) (v δ : Plane) (hδ : δ ∈ holeLattice W) :
    holeCovariogram W (v-δ) / (2*W.x*H) ≤ bothBlank W v := by
  let E := {z : Plane | colour W z = none ∧ colour W (z+v) = none}
  let C := cell W (3*H)
  have mB := (blank_closed W).measurableSet
  have mE : MeasurableSet E := mB.inter (mB.preimage (continuous_id.add continuous_const).measurable)
  have hpos : 0 < 2*W.x*H := by nlinarith [W.x_bounds.1,H_pos]
  have hpos' : 0 < 6*W.x*H := by linarith
  have finite : volume (E∩C) ≠ ⊤ := ne_top_of_le_ne_top (by
    rw [show C=cell W (3*H) from rfl,lattice_covolume]; exact ENNReal.ofReal_ne_top)
    (measure_mono inter_subset_right)
  have c := ENNReal.toReal_mono finite (three_copies W v δ hδ)
  rw [ENNReal.toReal_mul] at c
  have sign : holeCovariogram W (v-δ) ≤ holeCovariogram W (-(v-δ)) :=
    holeCovariogram_antitone W _ _ (by simp only [PiLp.neg_apply,abs_neg,le_refl]) (by simp only [PiLp.neg_apply,abs_neg,le_refl])
  change 3*(volume (holeOverlap W (-(v-δ)))).toReal ≤ (volume (E∩C)).toReal at c
  change (volume (holeOverlap W (v-δ))).toReal ≤ (volume (holeOverlap W (-(v-δ)))).toReal at sign
  change _ ≤ ((Placement.translationLaw W) (Placement.translationPoint ⁻¹' E)).toReal
  rw [← Measure.map_apply Placement.continuous_translationPoint.measurable mE,
    Placement.translationLaw_map,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply mE,
    ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal hpos'.le]
  change _ ≤ (6*W.x*H)⁻¹ * (volume (E∩C)).toReal
  rw [div_le_iff₀ hpos]
  have norm : (6*W.x*H)⁻¹*(volume (E∩C)).toReal*(2*W.x*H) = (volume (E∩C)).toReal/3 := by
    have hn : W.x ≠ 0 := by linarith [W.x_bounds.1]
    field_simp [hn,H_pos.ne']; ring
  rw [norm]
  change (volume (holeOverlap W (v-δ))).toReal ≤ _
  linarith

theorem bothBlank_max_lower (W : Datum) (v : Plane) :
    max (holeCovariogram W v) (holeCovariogram W (v-point 0 1)) /
      (2*W.x*H) ≤ bothBlank W v := by
  have a := bothBlank_lower W v 0 (holeLattice W).zero_mem
  have b := bothBlank_lower W v _ (vertical_unit_mem W)
  simp only [sub_zero] at a
  by_cases le : holeCovariogram W v ≤ holeCovariogram W (v-point 0 1)
  · simpa only [max_eq_right le] using b
  · simpa only [max_eq_left (le_of_not_ge le)] using a

end
end HadwigerNelson.Wave
