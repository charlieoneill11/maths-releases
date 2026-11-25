import HadwigerNelson.Centres.CandidateMetric
import HadwigerNelson.Centres.EmptyCaps
import HadwigerNelson.Centres.MinorDisk

/-! The four geometric conclusions for a center candidate, Lemma 47. -/

namespace HadwigerNelson.Centres
noncomputable section
open Placement Set

theorem minorArc_cap {X : Finset Plane} {u v : Plane} (ne : u≠v) (h : minorArc X u v) : EmptyCap X u v := by
  obtain ⟨p,hp,q,hq,a,b,empty⟩ := h
  refine ⟨ne,?_,?_⟩
  · intro z hx hu
    apply le_of_not_gt
    intro hv
    exact empty z hx ((minor_disk_iff p q u v z a.1 ne a.2.1 a.2.2.1 b.2.1 b.2.2.1 hu).mpr hv)
  · intro z hu hv
    have e := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (V:=Plane) finrank_euclideanSpace_fin ne a.1
      ((dist_comm p u).trans a.2.1) ((dist_comm q u).trans a.2.2.1) hu
      ((dist_comm p v).trans b.2.1) ((dist_comm q v).trans b.2.2.1) hv
    rcases e with rfl|rfl <;> assumption

theorem minorArc_distance_le_two {X : Finset Plane} {u v : Plane} (h : minorArc X u v) : dist u v≤2 := by
  obtain ⟨p,_,_,_,a,b,_⟩ := h
  have e := dist_triangle u p v
  rw [a.2.1,dist_comm p v,b.2.1] at e
  linarith

private def below (θ : ℝ) (u : Plane) : Plane := u-rotate (-θ) (verticalStep 0)

private theorem rotate_below (θ : ℝ) (u : Plane) : rotate θ (below θ u)=rotate θ u-verticalStep 0 := by
  rw [below,rotate_sub,unrotate]

private theorem below_inside {X D : Finset Plane} {p : Profile} {θ : ℝ} {v u : Plane} (C : candidate X D p θ v u) :
    dist (below θ u) v<1 := by
  obtain ⟨ho,minor,bounds,t,hw,h⟩ := C
  rw [← rotate_dist θ,rotate_below]
  apply aligned_disk h ho.2.2.2.1 (minorArc_distance_le_two minor) (lt_of_lt_of_le (by norm_num [δR]) bounds.1)
  simpa only [zero_add] using hw.trans (cone_half p bounds.1)

theorem candidate_geometry_proof (X D : Finset Plane) (p : Profile) (θ : ℝ) (v u : Plane)
    (cand : candidate X D p θ v u) :
    (∃ a ∈ X, ∃ b ∈ X, consecutive X u a b ∧ consecutive X v a b ∧
      inMinorInterior (Placement.rotate θ a) (Placement.rotate θ b) (Placement.rotate θ u)
        (Placement.rotate θ v) (Placement.rotate θ u-Wave.point 0 1)) ∧
    (∀ v', candidate X D p θ v' u → v'=v) ∧
    δR+δ < (Placement.rotate θ (u-v)) 1 ∧
    (2/100 < chord u v → ∀ x ∈ X, ¬ unitCandidate θ x u) := by
  obtain ⟨orient,minor,bounds,t,wide,align⟩ := cand
  have C : candidate X D p θ v u := ⟨orient,minor,bounds,t,wide,align⟩
  have ne := orient.2.2.2.1
  obtain ⟨a,ha,b,hb,cu,cv,empty⟩ := minor
  have minor' : minorArc X u v := ⟨a,ha,b,hb,cu,cv,empty⟩
  have inside := below_inside C
  have U : dist (below θ u) u=1 := by rw [← rotate_dist θ,rotate_below]; exact step_unit _ _
  have inject : Function.Injective (rotate θ) := fun x y e => dist_eq_zero.mp
    ((rotate_dist θ x y).symm.trans (by rw [e,dist_self]))
  have cap := minorArc_cap ne minor'
  refine ⟨⟨a,ha,b,hb,cu,cv,?_⟩,?_,?_,?_⟩
  · have h := (minor_disk_iff (rotate θ a) (rotate θ b) (rotate θ u) (rotate θ v)
        (rotate θ u-verticalStep 0) (inject.ne cu.1) (inject.ne ne)
        ((rotate_dist θ u a).trans cu.2.1) ((rotate_dist θ u b).trans cu.2.2.1)
        ((rotate_dist θ v a).trans cv.2.1) ((rotate_dist θ v b).trans cv.2.2.1) (step_unit _ _)).mpr
        (by rwa [← rotate_below,rotate_dist])
    simpa [verticalStep] using h
  · intro v' C'
    exact unique_empty_cap U ⟨a,ha,b,hb,cu.1,(dist_comm a u).trans cu.2.1,(dist_comm b u).trans cu.2.2.1⟩
      (minorArc_cap C'.1.2.2.2.1 C'.2.1) cap (below_inside C') inside
  · have h := congrArg (fun x : Plane => x 1) align
    change rotate θ (u-v) 1=dist u v*Real.cos t at h
    rw [h]
    have D := minorArc_distance_le_two minor'
    have diag : (chord u v)^2=4-(dist u v)^2 := Real.sq_sqrt (by nlinarith [dist_nonneg (x:=u) (y:=v)])
    have R : 1≤dist u v := by
      apply (sq_le_sq₀ zero_le_one dist_nonneg).mp
      have lsq : (chord u v)^2 ≤ (245/1000:ℝ)^2 :=
        pow_le_pow_left₀ (le_trans (by norm_num [δR]) bounds.1) bounds.2 2
      nlinarith only [diag,lsq]
    have small : |t|≤365/100000 := wide.trans (cone_small _ _)
    have t₂ : t^2≤(1:ℝ)^2 := sq_le_sq.mpr (by rw [abs_one]; linarith)
    have cosine : 1/2≤Real.cos t := by linarith [Real.one_sub_sq_div_two_le_cos (x:=t)]
    norm_num [δR,δ]
    linarith [mul_le_mul_of_nonneg_right R (by linarith : 0≤Real.cos t)]
  · intro med x hx unit
    obtain ⟨s,ws,es⟩ := unit
    have point : rotate θ x = rotate θ u-verticalStep s := by
      rw [rotate_sub] at es
      exact eq_sub_of_add_eq (eq_add_of_sub_eq' es).symm
    have xu : dist x u=1 := by rw [← rotate_dist θ,point]; exact step_unit _ _
    have width : |s+t| ≤ chord u v/2 := (abs_add_le _ _).trans <|
      (add_le_add ws wide).trans (medium_cone p med)
    have inner := aligned_disk align ne (minorArc_distance_le_two minor') (lt_trans (by norm_num) med) width
    apply (cap.empty x hx xu).not_gt
    rwa [← rotate_dist θ,point]

end
end HadwigerNelson.Centres
