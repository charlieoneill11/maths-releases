import HadwigerNelson.Crossings.CircleKnots
import HadwigerNelson.Crossings.UnitDegrees
import Mathlib.Data.Finset.Sort

/-! The cyclic order of the unit neighbours of a point, and the arcs joining
successive neighbours. These include the closing arc across the angle cut. -/

namespace HadwigerNelson.Crossings
noncomputable section
namespace CircleMarks
attribute [local instance] Classical.propDecidable

variable (X : Finset Plane) (c : Plane)

def neighbours : Finset Plane := X.filter (fun z => dist z c = 1)
def angles : Finset ℝ := (neighbours X c).image (circleAngle c)

theorem angles_card : (angles X c).card = unitDegree X c := by
  have inj : Set.InjOn (circleAngle c) (neighbours X c) := by
    intro p hp q hq eq
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := (Finset.mem_filter.mp hq).2
    exact (circlePoint_angle h1).symm.trans ((congrArg (circlePoint c) eq).trans (circlePoint_angle h2))
  rw [angles, Finset.card_image_of_injOn inj]
  simp [neighbours, unitDegree, dist_comm c]

def knot : Fin (unitDegree X c) ↪o ℝ :=
  (angles X c).orderEmbOfFin (angles_card X c)

theorem knot_neighbour (i : Fin (unitDegree X c)) :
    ∃ z ∈ X, dist z c = 1 ∧ circleAngle c z = knot X c i := by
  have h := (angles X c).orderEmbOfFin_mem (angles_card X c) i
  obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp h
  exact ⟨z,(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2,eq⟩

theorem knot_bounds (i : Fin (unitDegree X c)) : knot X c i ∈ Set.Ioc (-Real.pi) Real.pi := by
  obtain ⟨z,_,_,eq⟩ := knot_neighbour X c i
  rw [← eq]
  exact circleAngle_bounds c z

theorem spread (i j : Fin (unitDegree X c)) : knot X c i-knot X c j < 2*Real.pi := by
  linarith [(knot_bounds X c i).2,(knot_bounds X c j).1]

def mark (i : Fin (unitDegree X c)) : ↥X :=
  ⟨circlePoint c (knot X c i), by
    obtain ⟨z,hz,hc,eq⟩ := knot_neighbour X c i
    rwa [← eq,circlePoint_angle hc]⟩

theorem mark_inj : Function.Injective (mark X c) := by
  intro i j h
  apply (knot X c).injective
  exact circlePoint_inj_of_short (by linarith [spread X c j i]) (spread X c i j)
    (congrArg Subtype.val h)

theorem mark_surj {z : Plane} (hz : z ∈ X) (hc : dist z c = 1) :
    ∃ j, (mark X c j : Plane) = z := by
  have h : circleAngle c z ∈ angles X c :=
    Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz,hc⟩,rfl⟩
  have hm : circleAngle c z ∈ Set.range (knot X c) := by
    rwa [knot,Finset.range_orderEmbOfFin]
  obtain ⟨j,hj⟩ := hm
  exact ⟨j, (congrArg (circlePoint c) hj).trans (circlePoint_angle hc)⟩

def time (i : Fin (unitDegree X c)) (u : unitInterval) : ℝ :=
  arcAngle (knot X c i) (CircleKnots.stop (knot X c) i) u

def arc (i : Fin (unitDegree X c)) : unitInterval → Plane :=
  circleArc c (knot X c i) (CircleKnots.stop (knot X c) i)

theorem arc_continuous (i) : Continuous (arc X c i) := circleArc_continuous _ _ _
theorem arc_injective (hd : 2 ≤ unitDegree X c) (i) : Function.Injective (arc X c i) :=
  circleArc_injective c
    (CircleKnots.start_lt_stop _ (knot X c).strictMono (spread X c) i)
    (CircleKnots.short _ (knot X c).strictMono (spread X c) hd i)

@[simp] theorem arc_zero (i) : arc X c i 0 = mark X c i := circleArc_zero _ _ _

@[simp] theorem arc_one (i) : arc X c i 1 = mark X c (CircleKnots.next i) :=
  (circleArc_one _ _ _).trans (CircleKnots.stop_point _ c i)

theorem time_mem (i) {u} (h0 : u ≠ 0) (h1 : u ≠ 1) :
    time X c i u ∈ Set.Ioo (knot X c i) (CircleKnots.stop (knot X c) i) :=
  arcAngle_mem_interior _ _ (CircleKnots.start_lt_stop _ (knot X c).strictMono (spread X c) i) h0 h1

theorem time_period (i j) {u} (h0 : u ≠ 0) (h1 : u ≠ 1) :
    time X c i u ∈ Set.Ioo (knot X c (CircleKnots.first j)) (knot X c (CircleKnots.first j)+2*Real.pi) := by
  have hi := time_mem X c i h0 h1
  exact ⟨(CircleKnots.base_le _ (knot X c).strictMono j i).trans_lt hi.1,
    hi.2.trans_le (CircleKnots.stop_le_period _ (spread X c) i)⟩

theorem arc_avoids (i) {u} (h0 : u ≠ 0) (h1 : u ≠ 1) {z : Plane} (hz : z ∈ X) :
    arc X c i u ≠ z := by
  intro eq
  have hc : dist z c = 1 := eq ▸ dist_circlePoint c (time X c i u)
  obtain ⟨j,hj⟩ := mark_surj X c hz hc
  have h := time_period X c i i h0 h1
  have he : time X c i u = knot X c j := circlePoint_inj_of_short
    (by linarith [h.1,CircleKnots.mark_lt_period _ (spread X c) i j])
    (by linarith [h.2,CircleKnots.base_le _ (knot X c).strictMono i j]) (eq.trans hj.symm)
  exact CircleKnots.not_inside _ (knot X c).strictMono i j (he ▸ time_mem X c i h0 h1)

theorem arc_disjoint {i j} (hij : i ≠ j) {u v} (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hv0 : v ≠ 0) (hv1 : v ≠ 1) : arc X c i u ≠ arc X c j v := by
  intro eq
  have hi := time_period X c i i hu0 hu1
  have hj := time_period X c j i hv0 hv1
  have he : time X c i u = time X c j v := circlePoint_inj_of_short
    (by linarith [hi.1,hj.2]) (by linarith [hi.2,hj.1]) eq
  have hu := time_mem X c i hu0 hu1
  have hv := time_mem X c j hv0 hv1
  rcases lt_or_gt_of_ne hij with h|h
  · linarith [CircleKnots.stop_le_later _ (knot X c).strictMono h, hu.2,hv.1]
  · linarith [CircleKnots.stop_le_later _ (knot X c).strictMono h, hv.2,hu.1]

end CircleMarks
end
end HadwigerNelson.Crossings
