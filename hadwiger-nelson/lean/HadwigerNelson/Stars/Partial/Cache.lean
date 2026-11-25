import HadwigerNelson.Stars.Partial.Moments

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Span)
open Arithmetic (GaussianInt)

def ValidCache (cache : Cache) : Prop :=
  ∀ q i p, cache[(q,i)]? = some p → p=powerEntry q i

theorem empty_cache_valid : ValidCache {} := by simp [ValidCache]

theorem loadPowers_valid (cache : Cache) (valid : ValidCache cache) (q i : Nat) :
    ValidCache (loadPowers cache q i).1 ∧ (loadPowers cache q i).2=powerEntry q i := by
  cases entry : cache[(q,i)]? with
  | some p => simpa only [loadPowers,entry] using And.intro valid (valid _ _ _ entry)
  | none =>
    simp only [loadPowers,entry,and_true]

    intro u j p h
    simp only [Std.HashMap.getElem?_insert,beq_iff_eq] at h
    split at h
    · rename_i eq
      cases eq
      exact (Option.some.inj h).symm
    · exact valid _ _ _ h

def uncached (s : Span) : PairMoments :=
  ⟨s.coeff,powerEntry s.quadrant s.start,powerEntry s.quadrant s.stop⟩

theorem prepare_true (spans : Array Span) (cache : Cache) (valid : ValidCache cache) :
    ValidCache (prepare true spans cache).1 ∧
      (prepare true spans cache).2=spans.map uncached := by
  let step (st : Cache × Array PairMoments) (p : Span) :=
    let a := loadPowers st.1 p.quadrant p.start
    let b := loadPowers a.1 p.quadrant p.stop
    (b.1,st.2.push ⟨p.coeff,a.2,b.2⟩)
  have loop (xs : List Span) (cache : Cache) (acc : Array PairMoments) (hc : ValidCache cache) :
      ValidCache (xs.foldl step (cache,acc)).1 ∧
      (xs.foldl step (cache,acc)).2.toList = acc.toList++xs.map uncached := by
    induction xs generalizing cache acc with
    | nil => simp [hc]
    | cons p xs ih =>
      let a := loadPowers cache p.quadrant p.start
      let b := loadPowers a.1 p.quadrant p.stop
      have ha := loadPowers_valid cache hc p.quadrant p.start
      have hb := loadPowers_valid a.1 ha.1 p.quadrant p.stop
      have eq : (⟨p.coeff,a.2,b.2⟩ : PairMoments) = uncached p := by
        unfold uncached
        rw [show a.2 = _ from ha.2,show b.2 = _ from hb.2]
      obtain ⟨v,vs⟩ := ih b.1 (acc.push ⟨p.coeff,a.2,b.2⟩) hb.1
      refine ⟨v,vs.trans ?_⟩
      simp [eq]
  change ValidCache (spans.foldl step (cache,#[])).1 ∧ (spans.foldl step (cache,#[])).2 = spans.map uncached
  rw [←Array.foldl_toList]
  obtain ⟨p,r⟩ := loop spans.toList cache #[] valid
  exact ⟨p,Array.toList_inj.mp (by simpa using r)⟩

theorem row_cache (arcs : Array BoxCheck.Arc) (s : BoxCheck.Source) (cache : Cache)
    (valid : ValidCache cache) :
    ValidCache (row arcs s cache).1 ∧ (row arcs s cache).2=(row arcs s {}).2 := by
  by_cases zero : s.other=0
  · simp [row,zero,prepare,valid]
  · have a := prepare_true (runs s.box s.other) cache valid
    have b := prepare_true (runs s.box s.other) {} empty_cache_valid
    have nz : (s.other != 0) = true := bne_iff_ne.mpr zero
    simp only [row,nz,beq_iff_eq,zero,if_false,a.2,b.2,and_true]
    exact a.1

end HadwigerNelson.Stars.PartialCheck
