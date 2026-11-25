import HadwigerNelson.Crossings.Restriction
import Mathlib.Data.Nat.Lattice

namespace HadwigerNelson.Crossings

open Set
noncomputable section
variable {n m k l : ℕ} {G : Graph n m}

namespace Selection

/-- Each crossing retained by the subdrawing is an original crossing of the same arcs. -/
def eventMap (s : Selection G k l) (D : Drawing G) (p : Crossing (s.drawing D)) : Crossing D :=
  ⟨(s.edge p.val.1,s.edge p.val.2.1,p.val.2.2),s.edge.strictMono p.property.1,p.property.2⟩

theorem eventMap_injective (s : Selection G k l) (D : Drawing G) :
    Function.Injective (s.eventMap D) := by
  rintro ⟨⟨e,f,z⟩,h⟩ ⟨⟨i,j,w⟩,g⟩ he
  have eq := Subtype.mk.inj he
  change (s.edge e,s.edge f,z) = (s.edge i,s.edge j,w) at eq
  simp only [Prod.mk.injEq] at eq
  obtain ⟨a,b,c⟩ := eq
  cases s.edge.injective a
  cases s.edge.injective b
  cases c
  rfl

end Selection

/-- Orient the pair at a deleted edge by its edge label, as in the public crossing count. -/
def onMap (D : Drawing G) (e : Fin m) (p : On D e) : Crossing D :=
  if h : e < p.val.1 then ⟨(e,p.val.1,p.val.2),h,p.property.2⟩
  else ⟨(p.val.1,e,p.val.2),lt_of_le_of_ne (le_of_not_gt h) p.property.1,p.property.2.2,p.property.2.1⟩

theorem onMap_injective (D : Drawing G) (e : Fin m) : Function.Injective (onMap D e) := by
  rintro ⟨⟨f,z⟩,hf⟩ ⟨⟨g,w⟩,hg⟩ eq
  have eq' := congrArg Subtype.val eq
  by_cases h : e < f <;> by_cases h' : e < g <;>
    simp [onMap, h, h'] at eq'
  · obtain ⟨rfl,rfl⟩ := eq'; rfl
  · exact (hg.1 eq'.1.symm).elim
  · exact (hf.1 eq'.1).elim
  · obtain ⟨rfl,rfl⟩ := eq'; rfl

/-- Crossings on a removed edge and those retained in a subdrawing are disjoint subsets of
the original crossing events. The signed count counts meetings at triple points separately. -/
theorem deletion_bound (s : Selection G k l) (D : Drawing G) (e : Fin m)
    (hout : ∀ j, s.edge j ≠ e) (hD : D.FiniteIntersections) :
    (s.drawing D).crossingCount + D.crossingsOn e ≤ D.crossingCount := by
  letI : Finite (Crossing D) := (finite_events D hD).to_subtype
  letI : Finite (Crossing (s.drawing D)) := Finite.of_injective _ (s.eventMap_injective D)
  letI : Finite (On D e) := Finite.of_injective _ (onMap_injective D e)
  have inj : Function.Injective (Sum.elim (s.eventMap D) (onMap D e)) := by
    apply Sum.elim_injective.mpr
    refine ⟨s.eventMap_injective D,onMap_injective D e,?_⟩
    intro a b h
    have eq := congrArg Subtype.val h
    by_cases he : e < b.val.1
    · exact hout a.val.1 (congrArg Prod.fst (by simpa only [onMap,he,dif_pos] using eq))
    · exact hout a.val.2.1 (congrArg (fun p : Fin m × Fin m × Plane ↦ p.2.1)
        (by simpa only [onMap,he,dif_neg] using eq))
  have hc := Nat.card_le_card_of_injective _ inj
  simpa only [Nat.card_sum,card_crossing,card_on] using hc

/-- Theorem 26 derived from the signed linear lower bound and five-planarity. -/
theorem improved_lower (facts : CitedFacts) {n m : ℕ} (G : Graph n m)
    (simple : G.IsSimple) (hn : 3 ≤ n) :
    54 * (m : ℤ) - 266 * ((n : ℤ) - 2) ≤ 9 * (crossingNumber G : ℤ) := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases sparse : (m : ℤ) ≤ 7 * ((n : ℤ) - 2)
    · have := facts.crossing_lower G simple hn
      omega
    obtain ⟨D,good,optimal⟩ := facts.attained G simple
    have hi : ∃ e, 6 ≤ D.crossingsOn e := by
      by_contra! hall
      have five := facts.five_planar G simple hn D good (fun e ↦ by have := hall e; omega)
      omega
    obtain ⟨e,he⟩ := hi
    let E := Finset.univ.erase e
    let s := Selection.spanning G E
    have size : E.card = m-1 := by simp [E]
    have mpos : 0 < m := Fin.pos e
    have hlower := ih E.card (by omega) s.graph (s.simple simple)
    have hle := facts.le_drawing s.graph (s.simple simple) (s.drawing D) (s.finite D (good_finite good))
    have hout (j) : s.edge j ≠ e := (Finset.mem_erase.mp (E.orderEmbOfFin_mem rfl j)).1
    have removed := deletion_bound s D e hout (good_finite good)
    omega

end
end HadwigerNelson.Crossings
