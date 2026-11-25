import HadwigerNelson.Crossings.ChordSide
import HadwigerNelson.Crossings.Halving
import HadwigerNelson.Crossings.ArcIncidence

/-! Select one arc at each ordered endpoint pair. Every discarded arc is
charged to both orientations of a chord which is consecutive about two
different centers. -/

namespace HadwigerNelson
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

namespace Centres
open Crossings

def doubledPairs (X : Finset Plane) : ℕ := by
  classical
  exact (∑ p ∈ X, (X.filter fun q =>
    ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ consecutive X u p q ∧ consecutive X v p q).card) / 2

def retainedArcBound (n : ℕ) (m : ℝ) : ℤ :=
  ⌊(((n : ℝ)*(n-1 : ℝ) + m - 2*m^2/n) * fourProbability n 1317 +
      (266/9 : ℝ)*(1317-2)) / (6 * pairProbability n 1317)⌋

end Centres
namespace Crossings
open ParallelSlots Centres

variable {n m : ℕ}

def arcSlot (G : Graph n m) (b : Bool) : Finset (Fin m) := univ.filter fun e => bit G e = b

theorem arcSlot_sum (G : Graph n m) : (arcSlot G false).card+(arcSlot G true).card=m := by
  simpa [arcSlot] using (univ : Finset (Fin m)).card_filter_add_card_filter_not (fun e => bit G e = false)

theorem key_inj_slot (G : Graph n m) (hm : ∀ v w, multiplicity G v w ≤ 2) (b) {i j}
    (hi : i ∈ arcSlot G b) (hj : j ∈ arcSlot G b) (he : key G i = key G j) : i=j := by
  by_contra ne
  exact parallel_bits G hm ne he ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)

theorem arcSlot_simple (G : Graph n m) (hm : ∀ v w, multiplicity G v w ≤ 2) (b) :
    (Selection.spanning G (arcSlot G b)).graph.IsSimple := by
  intro i j h
  let S := arcSlot G b
  apply (S.orderEmbOfFin rfl).injective
  exact key_inj_slot G hm b (S.orderEmbOfFin_mem rfl i) (S.orderEmbOfFin_mem rfl j) h

private def orientedKey (G : Graph n m) (a : Fin m × Bool) : Fin n × Fin n :=
  if a.2 then (G.right a.1,G.left a.1) else key G a.1

private theorem orientedKey_inj (G : Graph n m) (hm : ∀ v w, multiplicity G v w ≤ 2)
    {a b : Fin m × Bool} (ha : a.1 ∈ arcSlot G true) (hb : b.1 ∈ arcSlot G true)
    (eq : orientedKey G a = orientedKey G b) : a=b := by
  rcases a with ⟨i,x⟩
  rcases b with ⟨j,y⟩
  cases x <;> cases y
  · exact Prod.ext (key_inj_slot G hm true ha hb eq) rfl
  · have h₁ : G.left i = G.right j := congrArg Prod.fst eq
    have h₂ : G.right i = G.left j := congrArg Prod.snd eq
    have h := G.ordered i
    rw [h₁,h₂] at h
    exact False.elim ((G.ordered j).not_gt h)
  · have h₁ : G.right i = G.left j := congrArg Prod.fst eq
    have h₂ : G.left i = G.right j := congrArg Prod.snd eq
    have h := G.ordered i
    rw [h₂,h₁] at h
    exact False.elim ((G.ordered j).not_gt h)
  · congr 1
    apply key_inj_slot G hm true ha hb
    exact Prod.ext (congrArg Prod.snd eq) (congrArg Prod.fst eq)

theorem discarded_le_doubled (X : Finset Plane) (hd : minNonisolatedDegree X 3) :
    (arcSlot (CircleDrawing.unitDrawing X hd).G true).card ≤ doubledPairs X := by
  let A := CircleDrawing.unitDrawing X hd
  let doubled (p q : Plane) := ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ consecutive X u p q ∧ consecutive X v p q
  let T : Finset (Plane × Plane) := (X ×ˢ X).filter (fun p => doubled p.1 p.2)
  let domain := (arcSlot A.G true) ×ˢ (univ : Finset Bool)
  let send (s : Fin (2*unitEdgeCount X) × Bool) := Prod.map A.D.vertex A.D.vertex (orientedKey A.G s)
  have original (v) : A.D.vertex v ∈ X := by
    have : A.D.vertex v ∈ Set.range A.D.vertex := ⟨v,rfl⟩
    rwa [A.vertex_set] at this
  have physical (e) (he : e ∈ arcSlot A.G true) :
      doubled (A.D.vertex (A.G.left e)) (A.D.vertex (A.G.right e)) := by
    have bit_eq := (mem_filter.mp he).2
    obtain ⟨f,hlt,hkey⟩ := of_decide_eq_true (show decide _ = true from bit_eq)
    have hl : A.G.left f = A.G.left e := congrArg Prod.fst hkey
    have hr : A.G.right f = A.G.right e := congrArg Prod.snd hkey
    have hc : (A.center f : Plane) ≠ A.center e :=
      fun h => hlt.ne (A.same_center_endpoint_inj (Subtype.ext h) hl hr)
    have cf := CircleDrawing.endpoints_consecutive X hd f
    change consecutive X (A.center f) (A.D.vertex (A.G.left f)) (A.D.vertex (A.G.right f)) at cf
    rw [hl,hr] at cf
    exact ⟨_,(A.center f).property,_,(A.center e).property,hc,cf,CircleDrawing.endpoints_consecutive X hd e⟩
  have upper : domain.card ≤ T.card := by
    apply card_le_card_of_injOn send
    · rintro ⟨e,b⟩ h
      have he := (mem_product.mp h).1
      have hp := physical e he
      apply mem_filter.mpr
      cases b
      · exact ⟨mem_product.mpr ⟨original _,original _⟩, hp⟩
      · obtain ⟨u,hu,v,hv,hne,h₁,h₂⟩ := hp
        exact ⟨mem_product.mpr ⟨original _,original _⟩,
          ⟨u,hu,v,hv,hne,consecutive_comm.mp h₁,consecutive_comm.mp h₂⟩⟩
    · intro a ha b hb eq
      apply orientedKey_inj A.G A.multiplicity_le_two (mem_product.mp ha).1 (mem_product.mp hb).1
      exact Prod.ext (A.D.vertex_injective (congrArg Prod.fst eq)) (A.D.vertex_injective (congrArg Prod.snd eq))
  have size : T.card = ∑ p ∈ X, (X.filter (doubled p)).card := by
    simp only [T,card_filter,sum_product]
  have dh : domain.card = (arcSlot A.G true).card*2 := by simp [domain]
  rw [size,dh] at upper
  exact Nat.le_div_iff_mul_le (by decide : 0<2) |>.2 upper

end Crossings
end
end HadwigerNelson
