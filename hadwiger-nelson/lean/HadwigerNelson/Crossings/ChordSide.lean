import HadwigerNelson.Crossings.Consecutive
import HadwigerNelson.Crossings.CircleDrawing

/-! The cyclic chords of the unit-circle drawing are consecutive in the
geometric half-plane sense of §6. -/

namespace HadwigerNelson
noncomputable section
namespace Centres

theorem consecutive_comm {X : Finset Plane} {c p q : Plane} :
    consecutive X c p q ↔ consecutive X c q p := by
  have flip (a b z : Plane) : side b a z = -side a b z := by unfold side; ring
  constructor <;> rintro ⟨hn,hp,hq,h | h⟩ <;> refine ⟨hn.symm,hq,hp,?_⟩
  · right; intro z hz hc; rw [flip]; exact neg_nonpos.mpr (h z hz hc)
  · left; intro z hz hc; rw [flip]; exact neg_nonneg.mpr (h z hz hc)
  · right; intro z hz hc; rw [flip]; exact neg_nonpos.mpr (h z hz hc)
  · left; intro z hz hc; rw [flip]; exact neg_nonneg.mpr (h z hz hc)

end Centres
namespace Crossings
open Centres

/-- The determinant of three cyclically ordered points on a unit circle. -/
theorem circle_side (c : Plane) (a b r : ℝ) :
    side (circlePoint c a) (circlePoint c b) (circlePoint c r) =
      4*Real.sin ((b-a)/2)*Real.sin ((r-b)/2)*Real.sin ((r-a)/2) := by
  let A := (b-a)/2
  let B := (r-b)/2
  let C := (r-a)/2
  have h₁ := Real.two_mul_sin_mul_cos C (A-B)
  have h₂ := Real.two_mul_sin_mul_cos C (A+B)
  rw [show C-(A-B)=r-b by dsimp [A,B,C]; ring,
      show C+(A-B)=b-a by dsimp [A,B,C]; ring] at h₁
  rw [show C-(A+B)=0 by dsimp [A,B,C]; ring,
      show C+(A+B)=r-a by dsimp [A,B,C]; ring,Real.sin_zero,zero_add] at h₂
  calc
    _ = Real.sin (b-a)+Real.sin (r-b)-Real.sin (r-a) := by
      simp [side,circlePoint,Wave.point,Real.sin_sub]; ring
    _ = 2*Real.sin C*(Real.cos (A-B)-Real.cos (A+B)) := by linarith only [h₁,h₂]
    _ = _ := by rw [← Real.two_mul_sin_mul_sin]; change _=4*Real.sin A*Real.sin B*Real.sin C; ring

theorem circle_side_nonneg (c : Plane) {a b r : ℝ} (hab : a ≤ b) (hbr : b ≤ r)
    (hra : r ≤ a+2*Real.pi) : 0 ≤ side (circlePoint c a) (circlePoint c b) (circlePoint c r) := by
  rw [circle_side]
  have bounds {x y : ℝ} (hx : a ≤ x) (hy : y ≤ r) (hlt : x ≤ y) : 0 ≤ Real.sin ((y-x)/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (bounds le_rfl hbr hab))
    (bounds hab le_rfl hbr)) (bounds le_rfl le_rfl (hab.trans hbr))

namespace CircleMarks

theorem mark_consecutive (X : Finset Plane) (c : Plane) (hd : 2 ≤ unitDegree X c) (i) :
    consecutive X c (mark X c i) (mark X c (CircleKnots.next i)) := by
  let q := knot X c
  let b := CircleKnots.stop q i
  have ends : circlePoint c b = mark X c (CircleKnots.next i) := CircleKnots.stop_point q c i
  have hab : q i ≤ b := (CircleKnots.start_lt_stop q q.strictMono (spread X c) i).le
  refine ⟨fun eq => CircleKnots.next_ne hd i (mark_inj X c (Subtype.ext eq)).symm,
    ?_,?_,Or.inl ?_⟩
  · rw [dist_comm]; exact dist_circlePoint _ _
  · rw [dist_comm]; exact dist_circlePoint _ _
  intro z hz hc
  obtain ⟨j,rfl⟩ := mark_surj X c hz (by rwa [dist_comm])
  rw [← ends]
  by_cases h : i < j
  · exact circle_side_nonneg c hab (CircleKnots.stop_le_later q q.strictMono h) (by linarith [spread X c j i])
  · have hq : q j ≤ q i := q.monotone (le_of_not_gt h)
    have hb : b ≤ q j + 2*Real.pi :=
      (CircleKnots.stop_le_period q (spread X c) i).trans (by linarith [CircleKnots.base_le q q.strictMono i j])
    have := circle_side_nonneg c hab hb (by linarith : q j+2*Real.pi ≤ q i+2*Real.pi)
    simpa only [circlePoint_add_period] using this

end CircleMarks
namespace CircleDrawing

theorem endpoints_consecutive (X : Finset Plane) (hd : minNonisolatedDegree X 3) (j) :
    let D := unitDrawing X hd
    consecutive X (D.center j) (D.D.vertex (D.G.left j)) (D.D.vertex (D.G.right j)) := by
  let e := (edgeIndex X).symm j
  have h := CircleMarks.mark_consecutive X (e.1 : Plane) (le_trans (by decide : 2 ≤ 3) (degree X hd e)) e.2
  change consecutive X e.1 (vertex X (min (source X e) (target X e))) (vertex X (max (source X e) (target X e)))
  by_cases order : source X e ≤ target X e
  · rw [min_eq_left order,max_eq_right order]
    simpa [vertex,source,target,label] using h
  · rw [min_eq_right (le_of_not_ge order),max_eq_left (le_of_not_ge order)]
    simpa [vertex,source,target,label] using consecutive_comm.mp h

end CircleDrawing
end Crossings
end
end HadwigerNelson
