import HadwigerNelson.Crossings.CircleParam
import HadwigerNelson.Crossings.CircleIntersections
import Mathlib.Topology.Order.IntermediateValue

/-! A point of the unit circle can lie in only one open cap between marked
neighbours. Sweep the circle in both directions starting at that point. The
first and last marked neighbours are the boundary of every such cap. -/

namespace HadwigerNelson.Centres
noncomputable section
open Crossings Set

/-- Both intersections with the supporting circle are marked; no marked
neighbour lies strictly inside the other unit disk. -/
structure EmptyCap (X : Finset Plane) (c v : Plane) : Prop where
  distinct : c ≠ v
  empty : ∀ z ∈ X, dist z c = 1 → 1 ≤ dist z v
  boundary : ∀ z, dist z c = 1 → dist z v = 1 → z ∈ X

private def sweepTime (c w z : Plane) : ℝ :=
  if circleAngle c w < circleAngle c z then circleAngle c z-circleAngle c w
  else circleAngle c z-circleAngle c w+2*Real.pi

private theorem sweepTime_mem {c w z : Plane} (hw : dist w c=1) (hz : dist z c=1) (ne : z ≠ w) :
    sweepTime c w z ∈ Ioo 0 (2*Real.pi) := by
  have a := circleAngle_bounds c z
  have b := circleAngle_bounds c w
  have ha : circleAngle c z ≠ circleAngle c w := fun h => ne
    ((circlePoint_angle hz).symm.trans ((congrArg (circlePoint c) h).trans (circlePoint_angle hw)))
  unfold sweepTime
  split
  · constructor <;> linarith [a.1,a.2,b.1,b.2]
  · rename_i h
    have hlt := lt_of_le_of_ne (le_of_not_gt h) ha
    constructor <;> linarith [a.1,a.2,b.1,b.2]

private theorem sweepTime_point {c w z : Plane} (hz : dist z c=1) :
    circlePoint c (circleAngle c w + sweepTime c w z)=z := by
  unfold sweepTime
  split
  · rw [show circleAngle c w+(circleAngle c z-circleAngle c w)=circleAngle c z by ring,circlePoint_angle hz]
  · rw [show circleAngle c w+(circleAngle c z-circleAngle c w+2*Real.pi)=circleAngle c z+2*Real.pi by ring,
      circlePoint_add_period,circlePoint_angle hz]

set_option maxHeartbeats 600000 in
theorem unique_empty_cap {X : Finset Plane} {c w v v' : Plane} (hw : dist w c=1)
    (marks : ∃ p∈X, ∃ q∈X, p≠q ∧ dist p c=1 ∧ dist q c=1)
    (H : EmptyCap X c v) (H' : EmptyCap X c v') (inside : dist w v < 1) (inside' : dist w v' < 1) :
    v=v' := by
  classical
  let T := (X.filter (fun z => dist z c=1)).image (sweepTime c w)
  let P (t : ℝ) := circlePoint c (circleAngle c w+t)
  let period := 2*Real.pi
  have curve : Continuous P := (circlePoint_continuous c).comp (continuous_const.add continuous_id)
  have zero : P 0 = w := by simpa [P] using circlePoint_angle hw
  have last : P period = w := (circlePoint_add_period c _).trans (circlePoint_angle hw)
  have on (t) : dist (P t) c = 1 := dist_circlePoint _ _
  have record {z : Plane} (hz : z∈X) (he : dist z c=1) : sweepTime c w z∈T :=
    Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,he⟩,rfl⟩
  have info {t} (ht : t∈T) : t ∈ Ioo 0 period ∧ P t ∈ X := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hz
    have ne : z≠w := fun eq => inside.not_ge (eq ▸ H.empty z hx he)
    refine ⟨sweepTime_mem hw he ne,?_⟩
    change circlePoint c _ ∈ X
    rwa [sweepTime_point he]
  have sweep_inj {s t} (hs : s∈Ioo 0 period) (ht : t∈Ioo 0 period) (eq : P s=P t) : s=t := by
    have e : circleAngle c w+s = circleAngle c w+t :=
      circlePoint_inj_of_short (by dsimp [period] at *; linarith [hs.1,ht.2])
        (by dsimp [period] at *; linarith [hs.2,ht.1]) eq
    exact add_left_cancel e
  obtain ⟨p,hp,q,hq,hpq,pc,qc⟩ := marks
  have nonempty : T.Nonempty := ⟨_,record hp pc⟩
  let a := T.min' nonempty
  let b := T.max' nonempty
  have ha : a∈T := T.min'_mem nonempty
  have hb : b∈T := T.max'_mem nonempty
  have different : P a ≠ P b := by
    intro e
    have same := sweep_inj (info ha).1 (info hb).1 e
    have all {t} (ht : t∈T) : a=t := le_antisymm (T.min'_le t ht) ((T.le_max' t ht).trans_eq same.symm)
    have ep := all (record hp pc)
    have eq := all (record hq qc)
    exact hpq ((sweepTime_point pc).symm.trans ((congrArg P (ep.symm.trans eq)).trans (sweepTime_point qc)))
  have both {y : Plane} (cap : EmptyCap X c y) (hin : dist w y < 1) :
      dist (P a) y=1 ∧ dist (P b) y=1 := by
    let f (t : ℝ) := dist (P t) y
    have cont : Continuous f := curve.dist continuous_const
    have at_zero : f 0<1 := by simpa [f,zero] using hin
    have at_end : f period<1 := by simpa [f,last] using hin
    have crossing {t} (ht : t∈Icc 0 period) (eq : f t=1) : t∈T := by
      have h₀ : 0 < t := lt_of_le_of_ne ht.1 (fun e => (e ▸ at_zero).ne eq)
      have h₁ : t < period := lt_of_le_of_ne ht.2 (fun e => at_end.ne (e ▸ eq))
      have nz := cap.boundary (P t) (on t) eq
      have member := record nz (on t)
      have same := sweep_inj (info member).1 ⟨h₀,h₁⟩ (sweepTime_point (on t))
      rwa [same] at member
    have at_a := cap.empty _ (info ha).2 (on a)
    have at_b := cap.empty _ (info hb).2 (on b)
    obtain ⟨s,hs,es⟩ := intermediate_value_Icc (info ha).1.1.le cont.continuousOn ⟨at_zero.le,at_a⟩
    obtain ⟨t,ht,et⟩ := intermediate_value_Icc' (info hb).1.2.le cont.continuousOn ⟨at_end.le,at_b⟩
    have hsT := crossing ⟨hs.1,hs.2.trans (info ha).1.2.le⟩ es
    have htT := crossing ⟨(info hb).1.1.le.trans ht.1,ht.2⟩ et
    have sa : s=a := le_antisymm hs.2 (T.min'_le s hsT)
    have tb : t=b := le_antisymm (T.le_max' t htT) ht.1
    exact ⟨(congrArg f sa.symm).trans es,(congrArg f tb.symm).trans et⟩
  obtain ⟨va,vb⟩ := both H inside
  obtain ⟨wa,wb⟩ := both H' inside'
  have choices := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (V := Plane) finrank_euclideanSpace_fin different H.distinct
    (dist_comm c _ |>.trans (on a)) ((dist_comm v _).trans va) ((dist_comm v' _).trans wa)
    ((dist_comm c _).trans (on b)) ((dist_comm v _).trans vb) ((dist_comm v' _).trans wb)
  exact ((choices.resolve_left H'.distinct.symm).symm)

end
end HadwigerNelson.Centres
