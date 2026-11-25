import HadwigerNelson.Centres.AdjacentMarks
import HadwigerNelson.Centres.BudgetDefs

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The two vertices on both unit circles exhaust their points of intersection. -/
theorem common_pair {a b p q : Plane} (ab : a ≠ b) (pq : p ≠ q)
    (pa : dist p a = 1) (pb : dist p b = 1) (qa : dist q a = 1) (qb : dist q b = 1)
    {x : Plane} (xa : dist x a = 1) (xb : dist x b = 1) : x=p ∨ x=q := by
  obtain ⟨T,size,mem⟩ := unit_intersections_le_two a b ab
  have tp := (mem p).mpr ⟨pa,pb⟩
  have tq := (mem q).mpr ⟨qa,qb⟩
  have tx := (mem x).mpr ⟨xa,xb⟩
  by_contra! ne
  exact size.not_gt (Finset.two_lt_card_iff.mpr ⟨x,p,q,tx,tp,tq,ne.1,ne.2,pq⟩)

theorem chord_eq_dist {u v p q : Plane} (uv : u ≠ v) (pq : p ≠ q) (cu : dist u p = 1)
    (du : dist u q = 1) (cv : dist v p = 1) (dv : dist v q = 1) : chord u v = dist p q := by
  symm
  exact (rhombus_geometry u v p q uv pq (by rwa [dist_comm]) (by rwa [dist_comm])
    (by rwa [dist_comm]) (by rwa [dist_comm])).2.1

abbrev Arc (X : Finset Plane) := CircleDrawing.Handle X
def head {X : Finset Plane} (e : Arc X) : ↥X := e.1
def start {X : Finset Plane} (e : Arc X) : Plane := CircleMarks.mark X e.1 e.2
def finish {X : Finset Plane} (e : Arc X) : Plane := CircleMarks.mark X e.1 (CircleKnots.next e.2)
def length {X : Finset Plane} (e : Arc X) : ℝ := CircleKnots.stop (CircleMarks.knot X e.1) e.2-CircleMarks.knot X e.1 e.2

def paired {X : Finset Plane} (e : Arc X) : Prop :=
  ∃ v ∈ X, v ≠ (head e:Plane) ∧ consecutive X v (start e) (finish e)

theorem start_mem {X : Finset Plane} (e : Arc X) : start e ∈ X := (CircleMarks.mark X e.1 e.2).property
theorem finish_mem {X : Finset Plane} (e : Arc X) : finish e ∈ X := (CircleMarks.mark X e.1 _).property

theorem arc_consecutive {X : Finset Plane} (hd : minNonisolatedDegree X 3) (e : Arc X) :
    consecutive X (head e) (start e) (finish e) :=
  CircleMarks.mark_consecutive X e.1 (by have := CircleDrawing.degree X hd e; omega) e.2

/-- Consecutive endpoints determine exactly one arc on a circle with at least three marks. -/
theorem endpoints_arc {X : Finset Plane} (c : ↥X) {p q : Plane} (pX : p ∈ X) (qX : q ∈ X)
    (cons : consecutive X c p q) :
    ∃ i : Fin (unitDegree X c), let e : Arc X := ⟨c,i⟩
      (start e = p ∧ finish e = q) ∨ (start e = q ∧ finish e = p) := by
  obtain ⟨i,hi⟩ := CircleMarks.mark_surj X c pX (by rw [dist_comm]; exact cons.2.1)
  obtain ⟨j,hj⟩ := CircleMarks.mark_surj X c qX (by rw [dist_comm]; exact cons.2.2.1)
  rw [←hi,←hj] at cons
  rcases CircleMarks.consecutive_adjacent X c i j cons with left|right
  · exact ⟨i,Or.inl ⟨hi,by change (CircleMarks.mark X c (CircleKnots.next i):Plane) = q; rwa [←left]⟩⟩
  · exact ⟨j,Or.inr ⟨hj,by change (CircleMarks.mark X c (CircleKnots.next j):Plane) = p; rwa [←right]⟩⟩

theorem index_eq {X : Finset Plane} (hd : minNonisolatedDegree X 3) {c : ↥X}
    (i j : Fin (unitDegree X c))
    (eq : let e : Arc X := ⟨c,i⟩; let f : Arc X := ⟨c,j⟩
      (start e= start f ∧ finish e=finish f) ∨ (start e=finish f ∧ finish e=start f)) : i=j := by
  rcases eq with ⟨a,_⟩|⟨a,b⟩
  · exact CircleMarks.mark_inj X c (Subtype.ext a)
  · have h₁ : i=CircleKnots.next j := CircleMarks.mark_inj X c (Subtype.ext a)
    have h₂ : CircleKnots.next i=j := CircleMarks.mark_inj X c (Subtype.ext b)
    have ne := CircleKnots.next_next_ne (CircleDrawing.degree X hd ⟨c,i⟩) i
    exact False.elim (ne (by rw [h₂,←h₁]))

theorem partner_unique {X : Finset Plane} {e : Arc X} {v w : Plane} (vu : v ≠ (head e:Plane))
    (wu : w ≠ (head e:Plane)) (c : consecutive X (head e) (start e) (finish e))
    (vC : consecutive X v (start e) (finish e)) (wC : consecutive X w (start e) (finish e)) : v=w := by
  exact ((common_pair c.1 vu vC.2.1 vC.2.2.1 c.2.1 c.2.2.1 wC.2.1 wC.2.2.1).resolve_right wu).symm

theorem arc_for_orientation {X D : Finset Plane} {v u : Plane} (h : orientation X D v u) :
    ∃ e : Arc X, (head e:Plane)=u ∧ v ≠ u ∧ consecutive X v (start e) (finish e) := by
  obtain ⟨_,_,uX,uv,p,px,q,qx,cu,cv⟩ := h
  obtain ⟨i,yes⟩ := endpoints_arc ⟨u,uX⟩ px qx cu
  refine ⟨⟨⟨u,uX⟩,i⟩,rfl,uv.symm,?_⟩
  rcases yes with ⟨a,b⟩|⟨a,b⟩
  · rwa [a,b]
  · rw [a,b]; exact consecutive_comm.mp cv

end
end HadwigerNelson.Centres
