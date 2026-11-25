import HadwigerNelson.Centres.ArcLabels
import HadwigerNelson.Centres.MinorDisk
import Mathlib.Tactic.LinearCombination

namespace HadwigerNelson.Centres
open Finset Crossings CircleKnots
noncomputable section

private theorem dist_sq (p q : Plane) : dist p q^2=(p 0-q 0)^2+(p 1-q 1)^2 := by
  simpa [Fin.sum_univ_two,Real.dist_eq,sq_abs] using EuclideanSpace.dist_sq_eq p q

private theorem exterior_of_side {p q u v z : Plane} (pq : p≠q) (uv : u≠v)
    (up : dist u p=1) (uq : dist u q=1) (vp : dist v p=1) (vq : dist v q=1)
    (zu : dist z u=1) (s : 0 ≤ side p q z) (l : 0 ≤ side p q u) : 1 ≤ dist z v := by
  obtain ⟨add,_,_⟩ := rhombus_geometry p q u v pq uv up uq vp vq
  have veq : v=p+q-u := by rw [add,add_sub_cancel_left]
  have identity : dist p q^2*(dist z v^2-dist z u^2)-4*side p q z*side p q u =
      (dist u p^2-dist u q^2)*(dist z p^2-dist z q^2) := by
    rw [veq]
    simp only [dist_sq,side,PiLp.sub_apply,PiLp.add_apply]
    ring
  rw [up,uq,sub_self,zero_mul,zu] at identity
  have pos := sq_pos_of_pos (dist_pos.mpr pq)
  have nonneg := (mul_nonneg_iff_of_pos_left pos).mp (show 0 ≤ dist p q^2*(dist z v^2-1^2) by
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) s) l])
  nlinarith [dist_nonneg (x:=z) (y:=v)]

private theorem mark_left {X : Finset Plane} (e : Arc X) (z : Plane) (zX : z ∈ X) (zu : dist z (head e) = 1) :
    0 ≤ side (start e) (finish e) z := by
  let t := CircleMarks.knot X e.1
  let i := e.2
  let b := stop t i
  obtain ⟨j,rfl⟩ := CircleMarks.mark_surj X e.1 zX zu
  change 0 ≤ side (circlePoint e.1 (t i)) (circlePoint e.1 (t (next i))) (circlePoint e.1 (t j))
  rw [← stop_point t e.1 i]
  have ini := (start_lt_stop t t.strictMono (CircleMarks.spread X e.1) i).le
  by_cases cmp : i < j
  · exact circle_side_nonneg _ ini (stop_le_later t t.strictMono cmp) (by linarith [CircleMarks.spread X e.1 j i])
  · have pre : t j ≤ t i := t.monotone (le_of_not_gt cmp)
    have ub : stop t i ≤ t j + 2*Real.pi :=
      (stop_le_period t (CircleMarks.spread X e.1) i).trans (by linarith [base_le t t.strictMono i j])
    simpa only [circlePoint_add_period] using circle_side_nonneg e.1 ini ub (by linarith : t j+2*Real.pi≤t i+2*Real.pi)

private theorem side_center (c : Plane) (s t : ℝ) :
    side (circlePoint c s) (circlePoint c t) c = Real.sin (t-s) := by
  simp [side,circlePoint,Real.sin_sub]; ring

theorem length_pos {X : Finset Plane} (e : Arc X) : 0 < length e :=
  sub_pos.mpr (start_lt_stop _ (CircleMarks.knot X e.1).strictMono (CircleMarks.spread X e.1) _)

theorem length_lt_turn {X : Finset Plane} (hd : minNonisolatedDegree X 3) (e : Arc X) : length e < 2*Real.pi :=
  short _ (CircleMarks.knot X e.1).strictMono (CircleMarks.spread X e.1)
    (by have := CircleDrawing.degree X hd e; omega) _

theorem chord_of_arc {X : Finset Plane} (hd : minNonisolatedDegree X 3) (e : Arc X) :
    dist (start e) (finish e) = 2*Real.sin (length e/2) := by
  have len := length_pos e
  have turn := length_lt_turn hd e
  let c := (e.1:Plane)
  let s := CircleMarks.knot X c e.2
  let t := stop (CircleMarks.knot X c) e.2
  have eq : finish e = circlePoint c t := (stop_point _ c _).symm
  have hc := Real.cos_two_mul_eq_one_sub ((t-s)/2)
  rw [show 2*((t-s)/2)=t-s by ring,Real.cos_sub] at hc
  have sq : dist (start e) (finish e)^2=(2*Real.sin (length e/2))^2 := by
    rw [eq,dist_sq]
    change (circlePoint c s 0-circlePoint c t 0)^2+(circlePoint c s 1-circlePoint c t 1)^2 = (2*Real.sin ((t-s)/2))^2
    simp [circlePoint,Wave.point]
    linear_combination (Real.sin_sq_add_cos_sq t)+(Real.sin_sq_add_cos_sq s)-2*hc
  exact (sq_eq_sq₀ dist_nonneg (mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)))).mp sq

theorem length_ge_chord {X : Finset Plane} (hd : minNonisolatedDegree X 3) (e : Arc X) :
    dist (start e) (finish e) ≤ length e := by
  rw [chord_of_arc hd]
  linarith [Real.sin_le (by linarith [length_pos e] : 0 ≤ length e/2)]

theorem oriented_length_le {X : Finset Plane} (hd : minNonisolatedDegree X 3) (e : Arc X)
    {v : Plane} (uv : (head e:Plane)≠v) (cons : consecutive X v (start e) (finish e)) :
    arcLength X (head e) v ≤ length e := by
  have yes := arc_consecutive hd e
  have radius := chord_eq_dist uv yes.1 yes.2.1 yes.2.2.1 cons.2.1 cons.2.2.1
  have sin := chord_of_arc hd e
  have turn := length_lt_turn hd e
  have len := length_pos e
  have eq : chord (head e) v/2=Real.sin (length e/2) := by rw [radius,sin]; ring
  by_cases small : length e ≤ Real.pi
  · have left : 0 ≤ side (start e) (finish e) (head e) := by
      change 0 ≤ side (circlePoint e.1 _) (circlePoint e.1 _) (e.1:Plane)
      rw [← stop_point (CircleMarks.knot X e.1) e.1 e.2, side_center]
      exact Real.sin_nonneg_of_nonneg_of_le_pi len.le small
    have minor : minorArc X (head e) v := by
      refine ⟨start e,start_mem e,finish e,finish_mem e,yes,cons,?_⟩
      intro z zX inside
      have zu := inside.1
      have lt := (minor_disk_iff _ _ _ _ _ yes.1 uv yes.2.1 yes.2.2.1 cons.2.1 cons.2.2.1 zu).mp inside
      exact lt.not_ge (exterior_of_side yes.1 uv yes.2.1 yes.2.2.1 cons.2.1 cons.2.2.1 zu (mark_left e z zX zu) left)
    rw [arcLength,if_pos minor,eq,Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)]
    linarith
  · have eq' : Real.arcsin (chord (head e) v/2) = Real.pi-length e/2 := by
      rw [eq,← Real.sin_pi_sub (length e/2),Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)]
    unfold arcLength; split <;> rw [eq'] <;> linarith

end
end HadwigerNelson.Centres
