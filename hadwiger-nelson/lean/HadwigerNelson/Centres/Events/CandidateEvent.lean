import HadwigerNelson.Centres.Events.SmallPlacement
import HadwigerNelson.Centres.CandidateGeometry
import HadwigerNelson.Placement.BlankHoles

/-! A candidate event leaves both centers blank. For a small chord a blank
unit tail would lie in the central hole and therefore in the forbidden open
minor arc. -/

namespace HadwigerNelson.Centres
open Placement Set MeasureTheory
noncomputable section

private theorem small_event (W : Wave.Datum) {X D : Finset Plane} {p : Profile} {θ : ℝ} {v u : Plane}
    (cand : candidate X D p θ v u) (τ : Translation) (i j : ℤ) (t : ℝ)
    (hi : chord u v≤2/100) (wide : |t|≤cone p (chord u v)) (al : aligned θ t v u)
    (hm : place (θ,τ) (midpoint u v)-Wave.holeLatticePoint W i j ∈ smallRegion W p (chord u v) t)
    (good : ∀ x∈X, colour W (θ,τ) x=none → place (θ,τ) x∈Wave.holeCopies W) :
    colour W (θ,τ) u=none ∧ colour W (θ,τ) v=none ∧
      ∀ x∈X, unitCandidate θ x u → (colour W (θ,τ) x).isSome=true := by
  let ζ := Wave.holeLatticePoint W i j
  let M := place (θ,τ) (midpoint u v)-ζ
  let U := place (θ,τ) u-ζ
  let V := place (θ,τ) v-ζ
  let l := chord u v
  let r := dist u v
  have lo : δR≤l := cand.2.2.1.1
  have ne := cand.1.2.2.2.1
  have hr := minorArc_distance_le_two cand.2.1
  have hr0 : 0≤r := dist_nonneg
  have diag : l^2=4-r^2 := Real.sq_sqrt (by dsimp only [r] at *; nlinarith [dist_nonneg (x:=u) (y:=v)])
  have frame : SmallPlacement M U V r t := placed_midpoint θ τ u v ζ t al
  obtain ⟨C⟩ := smallCell_exists W p lo hi wide hm
  have off := C.offsets lo hi hr0 hr diag
  obtain ⟨insideU,insideV⟩ := C.both_holes frame off
  refine ⟨shifted_copy_blank W i j 1 (by simpa using insideU),
    shifted_copy_blank W i j (-1) (by simpa using insideV),?_⟩
  intro x hx un
  obtain ⟨s,hs,es⟩ := un
  cases hc : colour W (θ,τ) x with
  | some z => rfl
  | none =>
    exfalso
    let T := place (θ,τ) x-ζ
    have xr : rotate θ x = rotate θ u-verticalStep s := by
      rw [rotate_sub] at es
      exact eq_sub_of_add_eq (eq_add_of_sub_eq' es).symm
    have shift : T=U-verticalStep s := by
      dsimp only [T,U,place]
      rw [xr]; abel
    have tx : T 0=U 0-Real.sin s := congrArg (fun z : Plane => z 0) shift
    have ty : T 1=U 1-Real.cos s := congrArg (fun z : Plane => z 1) shift
    obtain ⟨vert,bx,by'⟩ := C.tail_bounds frame off hs T tx ty
    have hole : T∈Wave.hole W := central_hole W i j (good x hx hc) bx by'
    have sin := C.tail_sine frame lo hi T tx ty vert hole
    have angle : |s+t|≤w+365/100000 :=
      (abs_add_le _ _).trans (add_le_add hs (wide.trans (cone_small _ _)))
    have cos : 0≤Real.cos (s+t) := Real.cos_nonneg_of_mem_Icc ⟨by
      linarith [(abs_le.mp angle).1,Real.two_le_pi,show w≤1/100 by norm_num [w]],by
      linarith [(abs_le.mp angle).2,Real.two_le_pi,show w≤1/100 by norm_num [w]]⟩
    have closer := aligned_disk_of_sine al ne hr sin cos
    have xu : dist x u=1 := by rw [← rotate_dist θ,xr]; exact step_unit _ _
    apply ((minorArc_cap ne cand.2.1).empty x hx xu).not_gt
    rwa [← rotate_dist θ,xr]

theorem candidate_event_sound (W : Wave.Datum) (X D : Finset Plane) (p : Profile) (θ : ℝ) (v u : Plane) :
    ∀ᵐ τ ∂translationLaw W, τ∈centreEvent W X D p θ v u →
      colour W (θ,τ) u=none ∧ colour W (θ,τ) v=none ∧
      ∀ x∈X, unitCandidate θ x u → (colour W (θ,τ) x).isSome=true := by
  have ae : ∀ᵐ τ ∂translationLaw W, ∀ x : ↥X, colour W (θ,τ) x=none → place (θ,τ) x∈Wave.holeCopies W :=
    ae_all_iff.mpr (fun x => Forest.placed_blank_in_holes W θ x)
  filter_upwards [ae] with τ good
  rintro ⟨cand,i,j,mem⟩
  by_cases hi : chord u v≤2/100
  · rw [if_pos hi] at mem
    obtain ⟨t,ht,al,inside⟩ := mem
    exact small_event W cand τ i j t hi ht al inside (fun x hx => good ⟨x,hx⟩)
  · rw [if_neg hi] at mem
    exact ⟨shifted_copy_blank W i j 2 (by simpa using mem.2),copy_blank W i j mem.1,
      fun x hx en => False.elim ((candidate_geometry_proof X D p θ v u cand).2.2.2 (lt_of_not_ge hi) x hx en)⟩

end
end HadwigerNelson.Centres
