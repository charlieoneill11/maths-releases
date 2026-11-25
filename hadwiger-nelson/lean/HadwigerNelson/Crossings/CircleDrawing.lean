import HadwigerNelson.Crossings.CircleMarks
import HadwigerNelson.Crossings.UnitArcDrawing

/-! The physical unit-circle drawing in Lemma 29, indexed by a center and a
successive pair of unit neighbours. Reversing a parameter interval where
needed puts the endpoint labels in the order required by `Graph`. -/

namespace HadwigerNelson.Crossings
noncomputable section
namespace CircleDrawing

variable (X : Finset Plane)

abbrev Handle := Σ c : ↥X, Fin (unitDegree X c)

def vertexIndex : ↥X ≃ Fin X.card := Fintype.equivFinOfCardEq (Fintype.card_coe X)

def edgeIndex : Handle X ≃ Fin (2*unitEdgeCount X) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_sigma]
    simp_rw [Fintype.card_fin]
    rw [Finset.sum_coe_sort]
    exact sum_unitDegree X)

def label (c : ↥X) (i : Fin (unitDegree X c)) : Fin X.card :=
  vertexIndex X (CircleMarks.mark X c i)

theorem label_inj (c : ↥X) : Function.Injective (label X c) :=
  (vertexIndex X).injective.comp (CircleMarks.mark_inj X c)

def source (e : Handle X) := label X e.1 e.2
def target (e : Handle X) := label X e.1 (CircleKnots.next e.2)

theorem degree (hd : minNonisolatedDegree X 3) (e : Handle X) : 3 ≤ unitDegree X e.1 := by
  have h := e.2.isLt
  rcases hd e.1 e.1.property with hx|hx <;> omega

theorem source_ne (hd : minNonisolatedDegree X 3) (e : Handle X) : source X e ≠ target X e :=
  fun eq => CircleKnots.next_ne (le_trans (by decide : 2 ≤ 3) (degree X hd e)) e.2
    ((label_inj X e.1 eq).symm)

def oriented (e : Handle X) : unitInterval → unitInterval :=
  if source X e ≤ target X e then id else unitInterval.symm

theorem oriented_continuous (e) : Continuous (oriented X e) := by
  unfold oriented; split <;> first | exact continuous_id | exact unitInterval.continuous_symm

theorem oriented_injective (e) : Function.Injective (oriented X e) := by
  unfold oriented; split <;> first | exact Function.injective_id | exact unitInterval.symm_bijective.injective

theorem oriented_interior (e) {t : unitInterval} (h0 : t ≠ 0) (h1 : t ≠ 1) :
    oriented X e t ≠ 0 ∧ oriented X e t ≠ 1 := by
  unfold oriented; split <;> simp [h0,h1,unitInterval.symm_eq_zero,unitInterval.symm_eq_one]

def vertex (v : Fin X.card) : Plane := (vertexIndex X).symm v

def arc (e : Handle X) (u : unitInterval) : Plane := CircleMarks.arc X e.1 e.2 (oriented X e u)

theorem arc_zero (e : Handle X) : arc X e 0 = vertex X (min (source X e) (target X e)) := by
  by_cases h : source X e ≤ target X e
  · rw [arc,oriented,if_pos h,min_eq_left h]
    simp [vertex,source,label]
  · rw [arc,oriented,if_neg h,min_eq_right (le_of_not_ge h)]
    simp [vertex,target,label]

theorem arc_one (e : Handle X) : arc X e 1 = vertex X (max (source X e) (target X e)) := by
  by_cases h : source X e ≤ target X e
  · rw [arc,oriented,if_pos h,max_eq_right h]
    simp [vertex,target,label]
  · rw [arc,oriented,if_neg h,max_eq_left (le_of_not_ge h)]
    simp [vertex,source,label]

theorem endpoint_inj (hd : minNonisolatedDegree X 3) {a b : Handle X} (hc : a.1 = b.1)
    (hl : min (source X a) (target X a) = min (source X b) (target X b))
    (hr : max (source X a) (target X a) = max (source X b) (target X b)) : a=b := by
  obtain ⟨c,i⟩ := a
  obtain ⟨d,j⟩ := b
  dsimp only at hc
  subst d
  change min (label X c i) (label X c (CircleKnots.next i)) = min (label X c j) (label X c (CircleKnots.next j)) at hl
  change max (label X c i) (label X c (CircleKnots.next i)) = max (label X c j) (label X c (CircleKnots.next j)) at hr
  apply congrArg (Sigma.mk c)
  let q := label X c
  have inj : Function.Injective q := label_inj X c
  have no_rev (h : i = CircleKnots.next j) (h' : CircleKnots.next i = j) : i = j :=
    False.elim ((CircleKnots.next_next_ne (degree X hd ⟨c,i⟩) i) ((congrArg CircleKnots.next h').trans h.symm))
  rcases le_total (q i) (q (CircleKnots.next i)) with h|h <;>
    rcases le_total (q j) (q (CircleKnots.next j)) with g|g
  · exact inj ((min_eq_left h).symm.trans (hl.trans (min_eq_left g)))
  · exact no_rev (inj ((min_eq_left h).symm.trans (hl.trans (min_eq_right g))))
      (inj ((max_eq_right h).symm.trans (hr.trans (max_eq_left g))))
  · exact no_rev (inj ((max_eq_left h).symm.trans (hr.trans (max_eq_right g))))
      (inj ((min_eq_right h).symm.trans (hl.trans (min_eq_left g))))
  · exact inj ((max_eq_left h).symm.trans (hr.trans (max_eq_left g)))

theorem same_center_disjoint {a b : Handle X} (hne : a ≠ b) (hc : a.1 = b.1)
    {u v : unitInterval} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    arc X a u ≠ arc X b v := by
  obtain ⟨c,i⟩ := a
  obtain ⟨d,j⟩ := b
  dsimp only at hc
  subst d
  have hij : i ≠ j := fun h => hne (congrArg (Sigma.mk c) h)
  have hu := oriented_interior X ⟨c,i⟩ hu0 hu1
  have hv := oriented_interior X ⟨c,j⟩ hv0 hv1
  exact CircleMarks.arc_disjoint X c hij hu.1 hu.2 hv.1 hv.2

def graph (hd : minNonisolatedDegree X 3) : Graph X.card (2*unitEdgeCount X) where
  left j := min (source X ((edgeIndex X).symm j)) (target X ((edgeIndex X).symm j))
  right j := max (source X ((edgeIndex X).symm j)) (target X ((edgeIndex X).symm j))
  ordered _ :=  min_lt_max.mpr (source_ne X hd _)

def drawing (hd : minNonisolatedDegree X 3) : Drawing (graph X hd) where
  vertex := vertex X
  vertex_injective := Subtype.val_injective.comp (vertexIndex X).symm.injective
  arc j := arc X ((edgeIndex X).symm j)
  arc_continuous _ :=  (CircleMarks.arc_continuous X _ _).comp (oriented_continuous X _)
  arc_injective _ :=  (CircleMarks.arc_injective X _ (le_trans (by decide : 2 ≤ 3) (degree X hd _)) _).comp
    (oriented_injective X _)
  at_zero _ :=  arc_zero X _
  at_one _ :=  arc_one X _
  avoids_vertices j _ hu0 hu1 v :=
    let hi := oriented_interior X ((edgeIndex X).symm j) hu0 hu1
    CircleMarks.arc_avoids X _ _ hi.1 hi.2 (((vertexIndex X).symm v).property)

def unitDrawing (hd : minNonisolatedDegree X 3) : UnitArcDrawing X where
  G := graph X hd
  D := drawing X hd
  center j := ((edgeIndex X).symm j).1
  vertex_set := by
    ext z
    constructor
    · rintro ⟨v,rfl⟩
      exact ((vertexIndex X).symm v).property
    · intro hz
      exact ⟨vertexIndex X ⟨z,hz⟩,congrArg Subtype.val ((vertexIndex X).symm_apply_apply _)⟩
  on_circle := by
    rintro e _ ⟨t,rfl⟩
    exact dist_circlePoint _ _
  same_center_disjoint := by
    intro e f hne hcenter
    apply Set.disjoint_left.mpr
    rintro _ ⟨u, hu, rfl⟩ ⟨v,hv,he⟩
    exact same_center_disjoint X (fun h => hne ((edgeIndex X).symm.injective h)) hcenter
      hu.1 hu.2 hv.1 hv.2 he.symm
  same_center_endpoint_inj _ hl hr := (edgeIndex X).symm.injective (endpoint_inj X hd ‹_› hl hr)

end CircleDrawing

/-- Every finite unit-distance graph of minimum nonisolated degree three has
the cyclic arc drawing used to prove the degree-variance inequality. -/
theorem unitArcDrawing_exists (X : Finset Plane) (hd : minNonisolatedDegree X 3) :
    Nonempty (UnitArcDrawing X) := ⟨CircleDrawing.unitDrawing X hd⟩

end
end HadwigerNelson.Crossings
