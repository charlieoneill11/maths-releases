import SevenCycle.Adjacent.SlabJoin
import SevenCycleRuntime.Frames

namespace SevenCycle.Adjacent.SlabJoin

open Proof Blueprint

private theorem fold_hit {α β : Type} (p : β → Prop) (step : β → α → β)
    (preserve : ∀ b a, p b → p (step b a)) (initial : β) (rows : List α)
    (hit : p initial ∨ ∃ a ∈ rows, ∀ b, p (step b a)) : p (rows.foldl step initial) := by
  induction rows generalizing initial with
  | nil => simpa using hit
  | cons a rows ih =>
    apply ih
    rcases hit with h | ⟨target, mem, enters⟩
    · exact Or.inl (preserve _ _ h)
    · rcases List.mem_cons.mp mem with rfl | later
      · exact Or.inl (enters initial)
      · exact Or.inr ⟨target,later,enters⟩

theorem frameMasks_covers {rows : Array (Array Nat)} {k : Fin 4} {p : AxisOrder} {s : Nat}
    {sites : Array Nat} (hs : sites ∈ rows) (hm : (p,s) ∈ transforms k) :
    FrameMask.mk (movedMask (oneBitMap p s) sites) ∈ frameMasks rows k := by
  let n := FrameMask.mk (movedMask (oneBitMap p s) sites)
  let fill := fun (init : Std.HashSet FrameMask) (t : AxisOrder × Nat) =>
    let m := oneBitMap t.1 t.2
    rows.foldl (init := init) fun seen r => seen.insert ⟨movedMask m r⟩
  have filled (init : Std.HashSet FrameMask) (t : AxisOrder × Nat)
      (h : n ∈ init ∨ ∃ r ∈ rows, FrameMask.mk (movedMask (oneBitMap t.1 t.2) r) = n) : n ∈ fill init t := by
    dsimp only [fill]
    rw [← Array.foldl_toList]
    apply fold_hit (fun v : Std.HashSet FrameMask => n ∈ v) _ (fun _ _ m => Std.HashSet.mem_insert.mpr (.inr m))
    rcases h with h | ⟨r,hr,e⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, Array.mem_toList_iff.mpr hr, fun _ => Std.HashSet.mem_insert.mpr (.inl (by simpa using e))⟩
  change n ∈ (transforms k).foldl fill {}
  rw [← Array.foldl_toList]
  exact fold_hit (fun v : Std.HashSet FrameMask => n ∈ v) fill (fun b a h => filled b a (.inl h))
    _ _ (.inr ⟨(p,s),Array.mem_toList_iff.mpr hm, fun b => filled b _ (.inr ⟨sites,hs,rfl⟩)⟩)

theorem rawRegion_eq (k : Fin 4) : rawRegion k = region k := by
  have same : ∀ v : ZMod 7, (v.val == 0 || v.val == 1 || v.val == 6) = decide (v = 6 ∨ v = 0 ∨ v = 1) := by decide
  apply Nat.eq_of_testBit_eq
  intro j
  rw [rawRegion,region,maskUpTo_bit,maskUpTo_bit]
  by_cases hj : j < 2401
  · simp only [hj, decide_true, Bool.true_and, coords_position ⟨j,hj⟩ k, inThree]
    exact same _
  · simp [hj]

theorem cached_eq (n : Nat) : cached regionMasks n = ofBits n := by
  simp only [cached, regionMasks, Vector.getElem_ofFn, digest, rawRegion_eq, ofBits, key]
  rfl

theorem domain_covers {rows : Array String} {k : Fin 4} {p : AxisOrder} {s : Nat}
    {row : String} (hr : row ∈ rows) (hm : (p,s) ∈ transforms k) :
    ofBits (movedMask (oneBitMap p s) (readSlab row)) ∈ (frameDomains rows)[k] := by
  change ofBits _ ∈ (Vector.ofFn _)[k.val]
  rw [Vector.getElem_ofFn, ← cached_eq]
  exact Array.mem_map_of_mem (Std.HashSet.mem_toArray.mpr (frameMasks_covers (Array.mem_map_of_mem hr) hm))

/-- A physical slab in the distinguished frame, or a signed transverse image
of an input row for any of the other three axes. -/
def ComesFrom (rows : Array String) (k : Fin 4) (set : Finset (Tuple 4)) : Prop :=
  ∃ row ∈ rows, ∃ t ∈ transforms k, Stores (movedMask (oneBitMap t.1 t.2) (readSlab row)) set

theorem checkFrames_sound {C : Finset (Tuple 4)} (hc : packing cycleStep C) (rows : Array String)
    (coverage : ∀ k, ComesFrom rows k (C.filter (inThree k))) {leaf : Nat → Bool}
    (ok : checkSlabs (frameDomains rows) neighborTable leaf = true) :
    ∃ bits : Fin 4 → Nat, (∀ k, Stores (bits k) (C.filter (inThree k))) ∧
      leaf (bits 0 ||| bits 1 ||| bits 2 ||| bits 3) = true := by
  choose row hr t ht hs using coverage
  let b := fun k => movedMask (oneBitMap (t k).1 (t k).2) (readSlab (row k))
  exact ⟨b, hs, checkSlabs_sound hc _ b hs (fun k => domain_covers (hr k) (ht k)) ok⟩

end SevenCycle.Adjacent.SlabJoin
