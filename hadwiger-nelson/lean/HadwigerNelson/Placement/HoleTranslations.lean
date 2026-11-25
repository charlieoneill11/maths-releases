import HadwigerNelson.Placement.CellMeasure
import HadwigerNelson.Stars.BoxIntegral

namespace HadwigerNelson.Placement
open Wave MeasureTheory Set
open scoped ENNReal Pointwise
noncomputable section

/-- A box of half-width 1/5 and half-height H/4 has disjoint translates
under the hole lattice. -/
theorem source_packing (W : Datum) (B : Set Plane)
    (size : ∀ z∈B, |z 0|≤1/5 ∧ |z 1|≤H/4) :
    Pairwise fun g h : holeLattice W => Disjoint (g +ᵥ B) (h +ᵥ B) := by
  intro g h ne
  apply disjoint_left.mpr
  rintro _ ⟨u,hu,rfl⟩ ⟨v,hv,e⟩
  obtain ⟨i,j,eg⟩ := (mem_holeLattice W g).mp g.2
  obtain ⟨k,l,eh⟩ := (mem_holeLattice W h).mp h.2
  change (h:Plane)+v=(g:Plane)+u at e
  rw [eg,eh] at e
  have x := congrArg (fun z : Plane => z 0) e
  have y := congrArg (fun z : Plane => z 1) e
  simp only [PiLp.add_apply,holeLatticePoint,point_fst,point_snd] at x y
  obtain ⟨u₁,u₂⟩ := size u hu
  obtain ⟨v₁,v₂⟩ := size v hv
  rw [abs_le] at u₁ u₂ v₁ v₂
  have apart {m n : ℤ} {p : ℝ} (hp : 0≤p) (lt : m<n) : p*((m:ℝ)+1)≤p*n :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast (show m+1≤n by omega)) hp
  have hx : 0≤2*W.x := by linarith [W.x_bounds.1]
  have ik : i=k := by
    by_contra bad
    rcases lt_or_gt_of_ne bad with lt | gt
    · linarith [apart hx lt,W.x_bounds.1,u₁.1,u₁.2,v₁.1,v₁.2]
    · linarith [apart hx gt,W.x_bounds.1,u₁.1,u₁.2,v₁.1,v₁.2]
  subst k
  have jl : j=l := by
    by_contra bad
    rcases lt_or_gt_of_ne bad with lt | gt
    · linarith [apart H_pos.le lt,H_pos,u₂.1,u₂.2,v₂.1,v₂.2]
    · linarith [apart H_pos.le gt,H_pos,u₂.1,u₂.2,v₂.1,v₂.2]
  exact ne (Subtype.ext (eg.trans (jl ▸ eh.symm)))

set_option maxHeartbeats 800000 in
/-- A uniformly translated point lies in the periodisation of a packed
source box with probability at least its normalised area. The source may
be shifted arbitrarily before placement. -/
theorem translate_probability_lower (W : Datum) (B : Set Plane) (offset : Plane)
    (E : Set Translation) (mb : MeasurableSet B)
    (pack : Pairwise fun g h : holeLattice W => Disjoint (g +ᵥ B) (h +ᵥ B))
    (cover : ∀ τ (g : holeLattice W), translationPoint τ + offset - (g:Plane) ∈ B → τ∈E) :
    volume.real B / (2*W.x*H) ≤ (translationLaw W).real E := by
  classical
  let D := -offset +ᵥ B
  let F : Set Plane := ⋃ g : holeLattice W, g +ᵥ D
  let S := cell W H
  let C := cell W (3*H)
  let δ (i : Fin 3) : Plane := point 0 ((i.val:ℝ)*H)
  let T (i : Fin 3) : Set Plane := F ∩ (δ i +ᵥ S)
  have md : MeasurableSet D := mb.const_vadd _
  have mf : MeasurableSet F := MeasurableSet.iUnion (fun g : holeLattice W => md.const_vadd g)
  have ms : MeasurableSet S := cell_measurable W H
  have mc : MeasurableSet C := cell_measurable W (3*H)
  have mt (i : Fin 3) : MeasurableSet (T i) := mf.inter (ms.const_vadd (δ i))
  have membership (z : Plane) : z∈F ↔ ∃ g : holeLattice W, z+offset-(g:Plane)∈B := by
    constructor
    · intro hz
      obtain ⟨g,hh⟩ := mem_iUnion.mp (show z∈⋃ k : holeLattice W,k +ᵥ D from hz)
      obtain ⟨d,hd,rfl⟩ := hh
      obtain ⟨b,hb,rfl⟩ := hd
      have e : (g:Plane)+(-offset+b)+offset-(g:Plane)=b := by abel
      exact ⟨g,e.symm ▸ hb⟩
    · rintro ⟨g,hg⟩
      exact mem_iUnion.mpr ⟨g,_,⟨_,hg,rfl⟩,by change ↑g+(-offset+(z+offset-↑g))=z; abel⟩
  have packD : Pairwise fun g h : holeLattice W => Disjoint (g +ᵥ D) (h +ᵥ D) := by
    intro g h ne
    apply disjoint_left.mpr
    rintro _ ⟨_,⟨b,hb,rfl⟩,rfl⟩ ⟨_,⟨a,ha,rfl⟩,e⟩
    apply disjoint_left.mp (pack ne) (show (g:Plane)+b ∈ g +ᵥ B from ⟨b,hb,rfl⟩)
    refine ⟨a,ha,?_⟩
    change ↑h+(-offset+a)=↑g+(-offset+b) at e
    change ↑h+a=↑g+b
    have f := congrArg (fun x : Plane => x + offset) e
    change ↑h+(-offset+a)+offset=↑g+(-offset+b)+offset at f
    abel_nf at f ⊢
    exact f
  have base : volume (F∩S) = volume B := (Stars.periodised_measure
    (holeLattice_fundamental W) ms md packD).trans (measure_vadd volume (-offset) B)
  have δmem (i : Fin 3) : δ i∈holeLattice W := by
    refine (mem_holeLattice W _).mpr ⟨0,i.val,?_⟩
    ext k; fin_cases k <;> simp [δ,holeLatticePoint,mul_comm]
  have invariant {z : Plane} (g : holeLattice W) : (g:Plane)+z∈F ↔ z∈F := by
    rw [membership,membership]
    constructor
    · rintro ⟨k,hk⟩
      have e : z+offset-((k:Plane)-g) = (g:Plane)+z+offset-(k:Plane) := by abel
      exact ⟨k-g,e.symm ▸ hk⟩
    · rintro ⟨k,hk⟩
      have e : (g:Plane)+z+offset-((g:Plane)+k) = z+offset-k := by abel
      exact ⟨g+k,e.symm ▸ hk⟩
  have area (i : Fin 3) : volume (T i) = volume B := by
    have e : T i = δ i +ᵥ (F∩S) := by
      ext z
      constructor
      · rintro ⟨fz,⟨x,sx,rfl⟩⟩
        exact ⟨x,⟨(invariant (g:=⟨δ i,δmem i⟩)).mp fz,sx⟩,rfl⟩
      · rintro ⟨x,⟨fx,sx⟩,rfl⟩
        exact ⟨(invariant (g:=⟨δ i,δmem i⟩)).mpr fx,⟨x,sx,rfl⟩⟩
    rw [e,measure_vadd,base]
  have bounds (i : Fin 3) {z : Plane} (h : z∈T i) :
      z 0∈Ico 0 (2*W.x) ∧ z 1∈Ico ((i.val:ℝ)*H) (((i.val:ℝ)+1)*H) := by
    obtain ⟨x,hx,e⟩ := h.2
    rw [←e]
    change 0+x 0∈_ ∧ ↑i.val*H+x 1∈_
    rw [zero_add]
    exact ⟨hx.1,by constructor <;> linarith [hx.2.1,hx.2.2]⟩
  have dis : Pairwise fun i j : Fin 3 => Disjoint (T i) (T j) := by
    intro i j ne
    apply disjoint_left.mpr
    intro z zi zj
    have a := (bounds i zi).2
    have b := (bounds j zj).2
    have gap {m n : Fin 3} (lt : m<n) : ((m.val:ℝ)+1)*H≤(n.val:ℝ)*H :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show m.val+1≤n.val from lt)) H_pos.le
    rcases lt_or_gt_of_ne ne with lt | gt
    · linarith [gap lt,a.2,b.1]
    · linarith [gap gt,b.2,a.1]
  have sum : volume (⋃ i, T i)=3*volume B := by
    rw [measure_iUnion dis mt,tsum_fintype,Fin.sum_univ_three,area,area,area]; ring
  have sub : (⋃ i, T i) ⊆ F∩C := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    obtain ⟨hx,l,r⟩ := bounds i hi
    have p : 0≤(i.val:ℝ)*H := mul_nonneg (Nat.cast_nonneg _) H_pos.le
    have b : ((i.val:ℝ)+1)*H≤3*H := mul_le_mul_of_nonneg_right (by exact_mod_cast (show i.val+1≤3 from i.isLt)) H_pos.le
    exact ⟨hi.1,hx,p.trans l,r.trans_le b⟩
  apply le_trans _ (measureReal_mono (s₁:=translationPoint ⁻¹' F) (s₂:=E) ?_)
  swap
  · intro τ h
    obtain ⟨g,hg⟩ := (membership _).mp h
    exact cover τ g hg
  have finite : volume (F∩C) ≠ ⊤ := ne_top_of_le_ne_top (by
    rw [show C=cell W (3*H) from rfl,lattice_covolume]; exact ENNReal.ofReal_ne_top)
    (measure_mono inter_subset_right)
  have m := measure_mono (μ:=volume) sub
  rw [sum] at m
  have mr := ENNReal.toReal_mono finite m
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat] at mr
  have p : 0<2*W.x*H := by nlinarith [W.x_bounds.1,H_pos]
  change _ ≤ ((translationLaw W) (translationPoint ⁻¹' F)).toReal
  rw [← Measure.map_apply continuous_translationPoint.measurable mf,
    translationLaw_map,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply mf,
    ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal (by linarith : 0≤6*W.x*H)]
  rw [div_le_iff₀ p]
  change (volume B).toReal ≤ (6*W.x*H)⁻¹*(volume (F∩C)).toReal*(2*W.x*H)
  have e : (6*W.x*H)⁻¹*(volume (F∩C)).toReal*(2*W.x*H) = (volume (F∩C)).toReal/3 := by
    have hn : W.x ≠ 0 := by linarith [W.x_bounds.1]
    field_simp [hn,H_pos.ne']; ring
  rw [e]; linarith

end
end HadwigerNelson.Placement
