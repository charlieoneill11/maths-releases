import SevenCycle.Adjacent.Middle
import SevenCycle.Adjacent.SupportSearch
import SevenCycleRuntime.AdjacentScan

namespace SevenCycle.Adjacent.Scan

open Proof Blueprint Bitsets

theorem getFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  rw [Vector.getElem_ofFn]

theorem checkPrepared_eq (idx : Contacts.Index) (s t : Cube) (gaps cs : Marks) (next : Cube → Bool) :
    checkPrepared (prepare idx s t) gaps cs next = Middle.checkMiddle s t idx gaps cs next := by
  simp only [checkPrepared, prepare, getFn, Middle.checkMiddle]
  rfl

theorem ordered_mem {idx : Contacts.Index} {s t : Cube} {a : Fin 3} {g c : Contacts.Height}
    (hg : g ∈ (#[1,2,3] : Array Contacts.Height))
    (h0 : idx.contains (Contacts.anchorKey s t a c) = true)
    (h1 : idx.contains (Contacts.anchorKey s t a (c-g)) = true) : (g,c) ∈ ordered idx s t a := by
  apply Array.mem_flatMap.mpr
  refine ⟨g,hg,Array.mem_map.mpr ⟨c,Array.mem_filter.mpr ⟨Array.mem_ofFn.mpr ⟨c,rfl⟩, ?_⟩,rfl⟩⟩
  simp only [getFn, h0, h1, Bool.and_self]

theorem checkPair_sound (atlas : Contacts.AtlasComplete)
    {C : SearchSpec.Points} (hc : packing cycleStep C) {s t u : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1) (lo : 16 ≤ (cubeSet u).card) (hi : (cubeSet u).card ≤ 19)
    (gaps cs : Marks) (valid : ∀ a, gaps.get a ∈ (#[1,2,3] : Array Contacts.Height))
    (full : ∀ a : Fin 3, cs.get a ∈ fullStarts C a.succ ∧ cs.get a - gaps.get a ∈ fullStarts C a.succ)
    {next : Visit} (ok : checkPair (Contacts.index orbitImages atlasPlanes) s t next = true) :
    ∃ r : Cube, cubeSet r = projectedLevel C 0 1 ∧ next s t gaps cs r = true := by
  let idx := Contacts.index orbitImages atlasPlanes
  have hit {a : Fin 3} (j : Contacts.Height) (h : j ∈ fullStarts C a.succ) :
      idx.contains (Contacts.anchorKey s t a j) = true := by
    obtain ⟨w, _, entry⟩ := Contacts.contact_covers atlas hc hs ht h
    by_contra hn
    have hm : Contacts.anchorKey s t a j ∉ idx := fun e => hn (Std.HashMap.contains_iff_mem.mpr e)
    change Contacts.middle w ∈ idx.getD (Contacts.anchorKey s t a j) #[] at entry
    rw [Std.HashMap.getD_eq_fallback hm] at entry
    exact Array.not_mem_empty _ entry
  have member (a : Fin 3) : (gaps.get a, cs.get a) ∈ ordered idx s t a :=
    ordered_mem (valid a) (hit _ (full a).1) (hit _ (full a).2)
  have filled (a : Fin 3) : (ordered idx s t a).isEmpty = false :=
    Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨_,member a⟩
  change checkPair idx s t next = true at ok
  simp only [checkPair, filled, Bool.false_or] at ok
  have leaf := Array.all_eq_true'.mp (Array.all_eq_true'.mp
    (Array.all_eq_true'.mp ok _ (member 0)) _ (member 1)) _ (member 2)
  have eta (x : Marks) : #v[x.get 0,x.get 1,x.get 2] = x := by
    apply Vector.ext
    intro n hn
    have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl | rfl <;> rfl
  simp only [eta, checkPrepared_eq] at leaf
  exact Middle.checkMiddle_sound atlas hc hs ht hu lo hi gaps cs full leaf

/-- The target classes can be sharded. Both supports and the transverse atlas
index use the literal 1,016 input representatives. -/
def checkClasses (classes : Array Cube) (next : Visit) : Bool :=
  let idx := Contacts.index orbitImages atlasPlanes
  checkSupportClasses classes (fun s t => checkPair idx s t next)

theorem checkClasses_sound (atlas : Contacts.AtlasComplete) {C : SearchSpec.Points}
    (hc : packing cycleStep C) {classes : Array Cube} (a : Fin atlasPlanes.size)
    {ref t : Cube} (hr : ref ∈ classes) (hgen : t ∈ orbitImages ref)
    (hs : TypeThree.RepresentsBand C 0 0 atlasPlanes[a]) (ht : TypeThree.RepresentsBand C 0 1 t)
    (sub : projectedLevel C 0 1 ⊆ cubeSet atlasPlanes[a] ∩ cubeSet t)
    (lo : 16 ≤ (projectedLevel C 0 1).card) (hi : (projectedLevel C 0 1).card ≤ 19)
    (gaps cs : Marks) (valid : ∀ i, gaps.get i ∈ (#[1,2,3] : Array Contacts.Height))
    (full : ∀ i : Fin 3, cs.get i ∈ fullStarts C i.succ ∧ cs.get i - gaps.get i ∈ fullStarts C i.succ)
    {next : Visit} (ok : checkClasses classes next = true) :
    ∃ r : Cube, cubeSet r = projectedLevel C 0 1 ∧ next atlasPlanes[a] t gaps cs r = true := by
  let u := buildCube fun x => decide (x ∈ projectedLevel C 0 1)
  have hu : cubeSet u = projectedLevel C 0 1 := by ext x; simp [u]
  exact checkPair_sound atlas hc hs ht hu (hu ▸ lo) (hu ▸ hi) gaps cs valid full
    (checkSupportClasses_retains classes (fun s t => checkPair (Contacts.index orbitImages atlasPlanes) s t next) ok a hr hgen sub lo)

end SevenCycle.Adjacent.Scan
