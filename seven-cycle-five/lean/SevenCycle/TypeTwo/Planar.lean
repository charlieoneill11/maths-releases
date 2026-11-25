import SevenCycleRuntime.TypeTwo
import SevenCycle.TypeTwo.DomainIndex

/-! ## Soundness of the representative bitsets used in the planar filter -/

namespace SevenCycle.TypeTwo.Planar

open SevenCycle.Bitsets (Cube)
open SevenCycle.Blueprint.SearchSpec

theorem fold_keeps {α β : Type*} (as : Array α) (put : β → α → β) (init : β)
    (P : β → Prop) (Q : α → Prop) (hs : ∀ b a, P b ∨ Q a → P (put b a))
    (h : P init ∨ ∃ a ∈ as, Q a) : P (as.foldl put init) := by
  have all := Array.foldl_induction (as := as) (f := put) (init := init)
    (motive := fun i m => P init ∨ (∃ j : Fin as.size, j.val < i ∧ Q as[j]) → P m)
    (by rintro (h | ⟨j,h,_⟩); exact h; exact False.elim (Nat.not_lt_zero _ h)) (by
      intro i m ih h
      apply hs
      rcases h with h | ⟨j,hj,hQ⟩
      · exact Or.inl (ih (Or.inl h))
      · by_cases he : i = j
        · subst j; exact Or.inr hQ
        · have : i.val ≠ j.val := fun eq => he (Fin.ext eq)
          exact Or.inl (ih (Or.inr ⟨j,by omega,hQ⟩)))
  apply all
  rcases h with h | ⟨a,ha,hQ⟩
  · exact Or.inl h
  · obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp ha
    exact Or.inr ⟨⟨j,hj⟩,hj,hQ⟩

def appendPartner (p : PartnerTable) (k : PairKey) : PartnerTable :=
  p.alter k.1 fun a => some ((a.getD #[]).push k.2)

def partnersOf (d : DomainIndex) : PartnerTable := d.keysArray.foldl appendPartner {}

theorem partnersOf_covers {d : DomainIndex} {x y : UInt64} {w : Cube}
    (hw : w ∈ bucket d (x,y)) : y ∈ (partnersOf d).getD x #[] := by
  have hkey : (x,y) ∈ d := by
    by_contra h
    simp [bucket, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_eq_none h] at hw
  apply fold_keeps d.keysArray appendPartner {} (fun p : PartnerTable => y ∈ p.getD x #[]) (fun k => k = (x,y)) _
    (Or.inr ⟨_,Std.HashMap.mem_keysArray.mpr hkey,rfl⟩)
  intro p k h
  by_cases eq : k.1 = x
  · rcases h with hp | rfl <;>
      simp_all [appendPartner, Std.HashMap.getD_eq_getD_getElem?, Array.mem_push]
  · rcases h with hp | rfl
    · simpa only [appendPartner, Std.HashMap.getD_alter, beq_iff_eq, eq, if_false] using hp
    · exact False.elim (eq rfl)

private theorem addBit_keeps (m : Std.HashMap UInt64 Nat) (k u : UInt64) (i j : Nat)
    (h : (m.getD k 0).testBit j ∨ u = k ∧ i = j) : ((addBit m i u).getD k 0).testBit j := by
  by_cases hu : u = k
  · subst u
    rcases h with hx | ⟨_,rfl⟩ <;>
      simp_all [addBit, Std.HashMap.getD_eq_getD_getElem?, Nat.testBit_or, Nat.testBit_two_pow]
  · rcases h with h | ⟨h,_⟩
    · simpa only [addBit, Std.HashMap.getD_alter, beq_iff_eq, hu, if_false] using h
    · contradiction

private theorem addPartners_keeps (m : Std.HashMap UInt64 Nat) (i j : Nat) (k : UInt64)
    (ps : Array UInt64) (h : (m.getD k 0).testBit j ∨ i = j ∧ k ∈ ps) :
    ((addPartners m i ps).getD k 0).testBit j := by
  apply fold_keeps ps (fun tbl u => addBit tbl i u) m
    (fun m : Std.HashMap UInt64 Nat => (m.getD k 0).testBit j) (fun u => u = k ∧ i = j)
    (fun tbl u => addBit_keeps tbl k u i j)
  rcases h with h | ⟨rfl, hk⟩
  · exact Or.inl h
  · exact Or.inr ⟨k,hk,rfl,rfl⟩

theorem candidateIndex_covers (p : PartnerTable) (s : Array Grid) (i : Fin s.size)
    (a : Fin 3) (j : Fin 7) (right : UInt64) (hr : right ∈ p.getD s[i][a][j] #[]) :
    (((candidateIndex p s)[a][j]).getD right 0).testBit i.val := by
  change (((candidateIndex p s)[a.val][j.val]).getD right 0).testBit i.val
  simp only [candidateIndex, Vector.getElem_ofFn]
  apply fold_keeps (Array.finRange s.size)
    (fun (m : Std.HashMap UInt64 Nat) (x : Fin s.size) => addPartners m x.val (p.getD s[x][a][j] #[]))
    {} (fun m : Std.HashMap UInt64 Nat => (m.getD right 0).testBit i.val) (fun x => x = i)
    _ (Or.inr ⟨i, Array.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩)
  intro tbl q h
  apply addPartners_keeps
  rcases h with h | rfl
  · exact Or.inl h
  · exact Or.inr ⟨rfl,hr⟩

private theorem eligibleAxis_bit {v : Vector Nat 7} {i : Nat} (p : Pick)
    (hl : v[p.first].testBit i) (hr : v[p.last].testBit i) : (eligibleAxis v).testBit i := by
  have hc : (v[p.first] &&& (v[p.first+2] ||| v[p.first+3])).testBit i := by
    simp only [Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true]
    constructor
    · exact hl
    · cases h : p.far
      · exact Or.inl (by simpa only [Pick.last, h, Bool.false_eq_true, ↓reduceIte] using hr)
      · exact Or.inr (by simpa only [Pick.last, h, ↓reduceIte] using hr)
  obtain ⟨t,far⟩ := p
  fin_cases t <;> simp [eligibleAxis] at hc ⊢ <;> tauto

def gridOf (cut : CutFn) (r : Cube) : Grid :=
  Vector.ofFn fun a => Vector.ofFn fun j : Fin 7 => cut r a j

/-- An actual pair of permitted starts on every axis retains the source
representative's bit, irrespective of the other 1,015 source bits. -/
theorem eligibleSources_retains (p : PartnerTable) (s : Array Grid) (i : Fin s.size) (t : Grid)
    (m : Vector Pick 3) (h : ∀ a : Fin 3, ∀ j ∈ ({m[a].first,m[a].last} : Finset (Fin 7)),
      t[a][j] ∈ p.getD s[i][a][j] #[]) :
    (eligibleSources (candidateIndex p s) t).testBit i.val := by
  have hh (a : Fin 3) : (eligibleAxis (Vector.ofFn fun j : Fin 7 =>
      (candidateIndex p s)[a][j].getD t[a][j] 0)).testBit i.val := by
    apply eligibleAxis_bit (m[a]) <;> rw [Fin.getElem_fin, Vector.getElem_ofFn]
    · exact candidateIndex_covers p s i a _ _ (h a _ (by simp))
    · exact candidateIndex_covers p s i a _ _ (h a _ (by simp))
  simp only [eligibleSources, Nat.testBit_and, Bool.and_eq_true]
  exact ⟨⟨hh 0,hh 1⟩,hh 2⟩

private theorem mem_picks (allowed : Fin 7 → Bool) (p : Pick)
    (h : allowed p.first) (h' : allowed p.last) : p ∈ picks allowed := by
  refine Array.mem_flatMap.mpr ⟨p.first, Array.mem_ofFn.mpr ⟨_, rfl⟩, ?_⟩
  apply Array.mem_filterMap.mpr
  refine ⟨p.far, ?_, ?_⟩
  · cases p.far <;> simp
  · obtain ⟨j,far⟩ := p
    simp only [h, h', Bool.and_true, if_true]

/-- Every marked placement with six admitted planar contacts is emitted, in
its original order of the three transverse axes. -/
theorem placements_retain (p : PartnerTable) (s : Array Grid) (i : Fin s.size) (t : Grid)
    (u v w : Pick)
    (h : ∀ a : Fin 3, ∀ j ∈ ({(#v[u,v,w])[a].first,(#v[u,v,w])[a].last} : Finset (Fin 7)),
      t[a][j] ∈ p.getD s[i][a][j] #[]) :
    #v[u,v,w] ∈ placements (candidateIndex p s) i.val t := by
  let good (a : Fin 3) (j : Fin 7) := ((candidateIndex p s)[a][j].getD t[a][j] 0).testBit i.val
  have hh (a : Fin 3) : (#v[u,v,w])[a] ∈ picks (good a) := by
    apply mem_picks
    · exact candidateIndex_covers p s i a _ _ (h a _ (by simp))
    · exact candidateIndex_covers p s i a _ _ (h a _ (by simp))
  exact Array.mem_flatMap.mpr ⟨u, hh 0, Array.mem_flatMap.mpr
    ⟨v, hh 1, Array.mem_map.mpr ⟨w,hh 2,rfl⟩⟩⟩

end SevenCycle.TypeTwo.Planar
