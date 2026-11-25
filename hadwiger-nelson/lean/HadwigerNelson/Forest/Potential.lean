import HadwigerNelson.Blueprint.Point.ForestDefs
import HadwigerNelson.Forest.Rotations
import Mathlib.Data.Finset.Max

/-! Root displacement, increasing height/depth, and the finite-forest inequality of Lemma 35. -/

namespace HadwigerNelson.Forest
open Centres Placement
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Parents with the specified short edges exist for every choice of the two maximal layers. -/
def Layers.ofMaximal {X R D : Finset Plane} (hR : maximalSeparated X R δR)
    (hD : maximalSeparated R D δ) : Layers X where
  R := R
  D := D
  maximalR := hR
  maximalD := hD
  parent := fun x => if hx : x ∈ D then x else if hr : x ∈ R then (hD.2.2 x hr hx).choose
    else if h : x ∈ X then (hR.2.2 x h hr).choose else x
  outer := by
    intro x hx hr
    have hd : x ∉ D := fun h => hr (hD.1 h)
    simpa [hd,hr,hx] using (hR.2.2 x hx hr).choose_spec
  inner := by
    intro x hr hd
    simpa [hr,hd] using (hD.2.2 x hr hd).choose_spec
  fixed := by intro x hx; simp [hx]

private theorem root_inner {X : Finset Plane} (L : Layers X) {x : Plane} (hx : x∈L.R) :
    L.parent (L.parent x) = L.parent x ∧ L.parent x ∈ L.D ∧ dist x (L.parent x) ≤ δ := by
  by_cases hd : x ∈ L.D
  · rw [L.fixed x hd]
    exact ⟨L.fixed x hd,hd,by norm_num [δ]⟩
  · obtain ⟨hp,hb⟩ := L.inner x hx hd
    exact ⟨L.fixed _ hp,hp,hb⟩

theorem root_bounds {X : Finset Plane} (L : Layers X) {x : Plane} (hx : x∈X) :
    L.parent (L.parent x) ∈ L.D ∧ dist x (L.parent (L.parent x)) ≤ δR+δ := by
  by_cases hr : x ∈ L.R
  · obtain ⟨hh,hp,hb⟩ := root_inner L hr
    rw [hh]
    exact ⟨hp,by linarith [show 0 ≤ δR by norm_num [δR]]⟩
  · obtain ⟨hp,hb⟩ := L.outer x hx hr
    obtain ⟨_,hd,hdist⟩ := root_inner L hp
    exact ⟨hd,(dist_triangle _ _ _).trans (add_le_add hb hdist)⟩

theorem centre_height_gain {X D : Finset Plane} {p : Profile} {θ : ℝ} {v u : Plane}
    (hc : candidate X D p θ v u) : δR+δ < rotate θ (u-v) 1 := by
  obtain ⟨_,_,hch,t,ht,align⟩ := hc
  change rotate θ (u-v) = _ at align
  have cone_bound : cone p (chord u v) ≤ 365/100000 := by
    unfold cone
    split
    · exact min_le_left ..
    · exact (min_le_left ..).trans (by norm_num)
  have small := ht.trans cone_bound
  have tSq : t^2 ≤ (365/100000:ℝ)^2 := by
    calc t^2 = |t|^2 := (sq_abs t).symm
         _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) small _
  have cos_t : (9/10:ℝ) < Real.cos t := by linarith [Real.one_sub_sq_div_two_le_cos (x:=t)]
  have dist_gt : 1 < dist u v := by
    by_contra! h
    have hd2 := pow_le_pow_left₀ dist_nonneg h 2
    have hc2 := Real.sq_sqrt (show 0 ≤ 4 - dist u v ^ 2 by nlinarith)
    have hch2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hch.2 2
    change Real.sqrt (4-dist u v ^ 2)^2 ≤ _ at hch2
    nlinarith
  rw [align]
  change δR+δ < dist u v * Real.cos t
  have := mul_lt_mul_of_pos_right dist_gt (by linarith : 0 < Real.cos t)
  norm_num [δR,δ] at *
  linarith

theorem candidate_increases {X : Finset Plane} (L : Layers X) (m : Mode) (p : Profile)
    (θ : ℝ) {x y : Plane} (hx : x ∈ X) (hy : y ∈ X) (hc : allCandidates L m p θ x y) :
    rootHeight L θ x < rootHeight L θ y ∨
      (rootHeight L θ x = rootHeight L θ y ∧ depth L x < depth L y) := by
  rcases hc with ⟨_,⟨hd,rfl⟩|⟨he, t,ht,disp⟩⟩ | ctr
  · right
    obtain ⟨hroot,_⟩ := root_bounds L hy
    refine ⟨?_,?_⟩
    · unfold rootHeight
      rw [L.fixed _ hroot]
    · by_cases h : L.parent y ∈ L.D <;> simp [depth,h,hd,hroot]
  · left
    have hr : x ∈ L.R := by
      cases m with
      | r => exact he
      | d => exact L.maximalD.1 he
      | centresOnly => exact False.elim (Finset.notMem_empty _ he)
    obtain ⟨eqroot,_,near⟩ := root_inner L hr
    have h1 := (abs_le.mp ((rotate_coord_difference_le θ x (L.parent x) 1).trans near)).1
    have h2 := (abs_le.mp ((rotate_coord_difference_le θ y _ 1).trans (root_bounds L hy).2)).2
    have dy := congrArg (fun z : Plane => z 1) disp
    rw [rotate_sub] at dy
    change rotate θ y 1-rotate θ x 1=Real.cos t at dy
    have sq : t^2≤w^2 := (sq_abs t).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) ht 2)
    unfold rootHeight
    rw [eqroot]
    norm_num [δR,δ,w] at h1 h2 sq
    linarith [Real.one_sub_sq_div_two_le_cos (x:=t)]
  · left
    have hd := ctr.1.2.1
    have gain := centre_height_gain ctr
    rw [rotate_sub] at gain
    change δR+δ < rotate θ y 1-rotate θ x 1 at gain
    have h := (abs_le.mp ((rotate_coord_difference_le θ x _ 1).trans (root_bounds L hx).2)).1
    unfold rootHeight
    rw [L.fixed _ hd,L.fixed _ hd]
    linarith

theorem incoming_forest {V : Type*} {X : Finset V} (h : V → ℝ) (d : V → ℕ)
    (F : Finset (V×V)) (grows : ∀ e ∈ F, h e.1 < h e.2 ∨ h e.1 = h e.2 ∧ d e.1 < d e.2)
    (unique : ∀ e ∈ F, ∀ f ∈ F, e.2=f.2 → e=f) (A : Finset V) (_ : A ⊆ X) (ha : A.Nonempty) :
    (F.filter (fun z => z.1 ∈ A ∧ z.2 ∈ A)).card < A.card := by
  classical
  let E := F.filter fun z => z.1 ∈ A ∧ z.2 ∈ A
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image A h ha
  let B := A.filter (fun x => h x = h v)
  obtain ⟨u,hu,umin⟩ := Finset.exists_min_image B d ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  obtain ⟨hua,uh⟩ := Finset.mem_filter.mp hu
  have miss : u ∉ E.image Prod.snd := by
    rintro hhit
    obtain ⟨⟨x,y⟩,he,rfl⟩ := Finset.mem_image.mp hhit
    obtain ⟨hef,hx,_⟩ := Finset.mem_filter.mp he
    rcases grows _ hef with lt | ⟨eq,dd⟩
    · exact (not_lt_of_ge (hmin x hx)) (lt.trans_eq uh)
    · exact (not_lt_of_ge (umin x (Finset.mem_filter.mpr ⟨hx,eq.trans uh⟩))) dd
  have sub : E.image Prod.snd ⊆ A := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp he).2.2
  have less := Finset.card_lt_card ((Finset.ssubset_iff_of_subset sub).mpr ⟨u,hua,miss⟩)
  have inject : Set.InjOn Prod.snd E := fun _ he _ hf => unique _ (Finset.mem_filter.mp he).1 _ (Finset.mem_filter.mp hf).1
  exact (Finset.card_image_of_injOn inject).symm.trans_lt less

end
end HadwigerNelson.Forest
