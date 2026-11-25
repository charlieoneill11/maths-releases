import HadwigerNelson.Stars.Directions
import HadwigerNelson.Stars.BoxIntegral
import HadwigerNelson.Wave.Geometry.Fundamental
import Mathlib.Analysis.Normed.Affine.MazurUlam

namespace HadwigerNelson.Stars
open MeasureTheory Set
open scoped Pointwise
noncomputable section

abbrev CopyIndex := Bool × Bool × Fin 3

def copyIso (i : CopyIndex) : Plane ≃ᵢ Plane := by
  rcases i with ⟨b,h,k⟩
  have tauSurj : Function.Surjective (Wave.tau k.val) := by
    intro z
    refine ⟨Wave.tau (-(k.val : ℤ)) z,?_⟩
    ext i
    fin_cases i <;> simp [Wave.tau]
  let T : Plane ≃ᵢ Plane := { Equiv.ofBijective _ ⟨(Wave.tau_isometry k.val).injective,tauSurj⟩
    with isometry_toFun := Wave.tau_isometry k.val }
  let R : Plane ≃ᵢ Plane := { Wave.sigma1_involutive.toPerm _ with
    isometry_toFun := Wave.sigma1_isometry }
  let S : Plane ≃ᵢ Plane := { Wave.sigma2_involutive.toPerm _ with
    isometry_toFun := Wave.sigma2_isometry }
  exact ((if h then R else IsometryEquiv.refl Plane).trans
    (if b then S else IsometryEquiv.refl Plane)).trans T

theorem copyIso_apply (b h : Bool) (k : Fin 3) (z : Plane) :
    copyIso (b,h,k) z = copyMap b h k z := by cases b <;> cases h <;> rfl

theorem copy_preserving (i : CopyIndex) : MeasurePreserving (copyIso i) volume volume := by
  let a := (copyIso i).toRealAffineIsometryEquiv
  have heq : (copyIso i : Plane → Plane) = (fun p : Plane => p + a 0) ∘ a.linearIsometryEquiv := by
    funext p
    simpa using a.map_vadd (0 : Plane) p
  rw [heq]
  exact (measurePreserving_add_right volume (a 0)).comp a.linearIsometryEquiv.measurePreserving

/-- A physical bound can be transferred from a representative to its image,
including when the exceptional set is merely null. -/
theorem copy_ae_iff (i : CopyIndex) (P : Plane → Prop) :
    (∀ᵐ z ∂volume, P z) ↔ ∀ᵐ z ∂volume, P (copyIso i z) := by
  have emb : MeasurableEmbedding (copyIso i) := (copyIso i).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  calc
    _ ↔ (∀ᵐ z ∂volume.map (copyIso i), P z) := by rw [(copy_preserving i).map_eq]
    _ ↔ _ := emb.ae_map_iff

theorem copy_volume (i : CopyIndex) {B : Set Plane} (hm : MeasurableSet B) :
    volume (copyIso i '' B) = volume B := by
  let e := (copyIso i).toHomeomorph.toMeasurableEquiv
  have mb : MeasurableSet (e '' B) := e.measurableEmbedding.measurableSet_image' hm
  have eq := (copy_preserving i).measure_preimage mb.nullMeasurableSet
  change volume ((copyIso i) ⁻¹' ((copyIso i) '' B)) = volume ((copyIso i) '' B) at eq
  simpa only [Set.preimage_image_eq _ (copyIso i).injective] using eq.symm

theorem copy_half (i : CopyIndex) {W : Wave.Datum} {p : Plane} (hp : p ∈ Wave.halfTile W false) :
    copyIso i p ∈ Wave.halfCopy W i.1 i.2.1 i.2.2 := by
  rcases i with ⟨b,h,k⟩
  rw [copyIso_apply]
  cases h
  · exact ⟨p,hp,rfl⟩
  · exact ⟨Wave.sigma1 p,Wave.sigma1_low W ▸ Set.mem_image_of_mem _ hp,rfl⟩

/-- Interior boxes cut from the lower half-tile give disjoint representatives
over all twelve copies and all period translates. -/
theorem copy_pack {ι : Type*} (W : Wave.Datum) (I : Finset ι) (B : ι → Set Plane)
    (inside : ∀ j ∈ I, B j ⊆ Wave.halfTile W false)
    (apart : ∀ i ∈ I, ∀ j ∈ I, ∀ z, z ∈ B i → z ∈ B j → i=j)
    (u w : CopyIndex × ι) (hu : u.2 ∈ I) (hw : w.2 ∈ I)
    (g h : Wave.lattice W) (x : Plane)
    (hx : x ∈ g +ᵥ (copyIso u.1 '' B u.2)) (hy : x ∈ h +ᵥ (copyIso w.1 '' B w.2)) :
    u=w ∧ g=h := by
  obtain ⟨_,⟨z,hz,rfl⟩,rfl⟩ := hx
  obtain ⟨_,⟨t,ht,rfl⟩,he⟩ := hy
  change (h : Plane) + copyIso w.1 t = (g : Plane) + copyIso u.1 z at he
  have move : copyIso u.1 z + ((g : Plane)-h) = copyIso w.1 t := by
    calc
      _ = ((g : Plane) + copyIso u.1 z) - h := by abel
      _ = _ := by rw [← he]; abel
  have hw' := copy_half w.1 (inside _ hw ht)
  rw [← move] at hw'
  have uniq := Wave.halfCopy_unique ((Wave.lattice W).sub_mem g.property h.property)
    (copy_half u.1 (inside _ hu hz)) hw'
  have ui : u.1 = w.1 := Prod.ext uniq.1 (Prod.ext uniq.2.1 uniq.2.2.1)
  have gh : g=h := Subtype.ext (sub_eq_zero.mp uniq.2.2.2)
  rw [uniq.2.2.2,add_zero,ui] at move
  have zt := (copyIso w.1).injective move
  exact ⟨Prod.ext ui (apart _ hu _ hw z hz (zt ▸ ht)),gh⟩

private theorem sum_twelve {ι : Type*} (I : Finset ι) (M : ι → ℝ) :
    (∑ e ∈ (Finset.univ : Finset CopyIndex) ×ˢ I, M e.2) = 12 * ∑ j ∈ I, M j := by
  rw [Finset.sum_product]
  simp [show Fintype.card CopyIndex = 12 by decide]

/-- Integrate all twelve congruent copies of the disjoint lower-half boxes
inside one fundamental cell, allowing each bound to fail on its own null set. -/
theorem twelve_copy_sum {ι : Type*} (W : Wave.Datum) (I : Finset ι)
    (B : ι → Set Plane) (c : ι → ℝ) (F : Plane → ℝ)
    (meas : ∀ j ∈ I, MeasurableSet (B j))
    (inside : ∀ j ∈ I, B j ⊆ Wave.halfTile W false)
    (apart : ∀ i ∈ I, ∀ j ∈ I, ∀ z, z ∈ B i → z ∈ B j → i=j)
    (period : ∀ g : Wave.lattice W, ∀ z, F ((g:Plane)+z) = F z)
    (mf : Measurable F) (hf : IntegrableOn F (Wave.cell W (3*Wave.H)) volume)
    (pos : 0 ≤ᵐ[volume.restrict (Wave.cell W (3*Wave.H))] F)
    (bounds : ∀ k : CopyIndex, ∀ j ∈ I, ∀ᵐ z ∂volume, z∈copyIso k '' B j → c j≤F z) :
    12 * (∑ j ∈ I, volume.real (B j) * c j) ≤ ∫ z in Wave.cell W (3*Wave.H), F z := by
  classical
  letI : IsFiniteMeasure (volume.restrict (Wave.cell W (3*Wave.H))) :=
    isFiniteMeasure_restrict.mpr (by rw [Wave.lattice_covolume]; exact ENNReal.ofReal_ne_top)
  let S := (Finset.univ : Finset CopyIndex) ×ˢ I
  let A (e : CopyIndex × ι) := copyIso e.1 '' B e.2
  have hj {e : CopyIndex × ι} (h : e∈S) : e.2∈I := (Finset.mem_product.mp h).2
  have mA (e : CopyIndex × ι) (he : e∈S) : MeasurableSet (A e) :=
    (copyIso e.1).toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image' (meas _ (hj he))
  have est := periodised_box_sum (Wave.lattice_fundamental W) (Wave.cell_measurable ..)
    S A (fun e => c e.2) F mA
    (fun u hu w hw => copy_pack W I B inside apart u w (hj hu) (hj hw))
    period mf hf pos (fun e he => bounds e.1 e.2 (hj he))
  have eqs : (∑ e ∈ S, volume.real (A e) * c e.2) = 12 * ∑ j ∈ I, volume.real (B j) * c j := by
    calc
      _ = ∑ e ∈ S, volume.real (B e.2) * c e.2 := by
        refine Finset.sum_congr rfl fun e he => ?_
        dsimp only [Measure.real,A]
        rw [copy_volume e.1 (meas _ (hj he))]
      _ = _ := sum_twelve I (fun j => volume.real (B j) * c j)
  rwa [eqs] at est

end
end HadwigerNelson.Stars
