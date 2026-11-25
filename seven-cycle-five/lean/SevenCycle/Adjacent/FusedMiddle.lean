import SevenCycle.Adjacent.Scan
import SevenCycle.Adjacent.Visible

namespace SevenCycle.Adjacent.ScanFused

open Proof Blueprint Bitsets
open Scan (Marks Visit)

private def scopes (rows : List Middle.Choices) (start : Nat) : Nat :=
  rows.foldl (fun f w => f ||| w.scope) start

private theorem scope_bit {α : Type} (rows : List α) (row : α → Middle.Choices) (start i : Nat) :
    (scopes (rows.map row) start).testBit i =
      (start.testBit i || rows.any (fun k => (row k).scope.testBit i)) := by
  induction rows generalizing start with
  | nil => simp [scopes]
  | cons a as ih =>
    change (scopes (as.map row) (start ||| (row a).scope)).testBit i = _
    rw [ih, Nat.testBit_or]
    simp [Bool.or_assoc]

private theorem materialize_mono (xs : Array Middle.Site) {a b : Nat}
    (sub : ∀ i, a.testBit i = true → b.testBit i = true) :
    cubeSet (Middle.materialize xs a) ⊆ cubeSet (Middle.materialize xs b) := by
  intro x hx
  let v := Middle.Site.ofWord x
  have hv : v.word = x := Middle.Site.word_ofWord x
  rw [← hv, ← Middle.occupied_iff, Middle.materialize_mem] at hx ⊢
  obtain ⟨i,hi,h⟩ := hx
  exact ⟨i,hi,sub i h⟩

private theorem decode_visible (s u : Cube) (hu : cubeSet u ⊆ cubeSet s) (gaps cs : Marks)
    (scope : Nat) (hscope : ∀ i (v : Middle.Site), (Middle.sites s)[i]? = some v →
      scope.testBit i = covered gaps cs v.word) :
    let xs := Middle.sites s
    cubeSet (Middle.materialize xs (Middle.flags xs (Middle.occupied u) &&& scope)) =
      (cubeSet u).filter (fun x => covered gaps cs x) := by
  ext x
  let v := Middle.Site.ofWord x
  have hv : v.word = x := Middle.Site.word_ofWord x
  rw [← hv, ← Middle.occupied_iff, Middle.materialize_mem, Finset.mem_filter, ← Middle.occupied_iff]
  constructor
  · rintro ⟨i,hi,h⟩
    simpa [Nat.testBit_and,Middle.flags_bit,hi,hscope i v hi] using h
  · rintro ⟨h, vis⟩
    have hm := (Middle.mem_sites v s).mpr ((Middle.occupied_iff s v).mpr (hu ((Middle.occupied_iff u v).mp h)))
    obtain ⟨i,hi,he⟩ := Array.mem_iff_getElem.mp hm
    have e : (Middle.sites s)[i]? = some v := by rw [Array.getElem?_eq_getElem hi, he]
    exact ⟨i,e,by simp [Nat.testBit_and,Middle.flags_bit,e,h,hscope i v e,vis]⟩

set_option maxHeartbeats 800000 in
theorem checked_sound (atlas : Contacts.AtlasComplete)
    {C : SearchSpec.Points} (hc : packing cycleStep C) {s t u : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1) (lo : 16 ≤ (cubeSet u).card) (hi : (cubeSet u).card ≤ 19)
    (gaps cs : Marks) (full : ∀ a : Fin 3, cs.get a ∈ fullStarts C a.succ ∧
      cs.get a - gaps.get a ∈ fullStarts C a.succ)
    {gate leaf : Cube → Bool}
    (ok : checked (Scan.prepare (Contacts.index orbitImages atlasPlanes) s t) gaps cs gate leaf = true) :
    ∃ v : Cube, cubeSet v = (projectedLevel C 0 1).filter (fun x => covered gaps cs x) ∧
      (gate v = true → ∃ r : Cube, cubeSet r = projectedLevel C 0 1 ∧ leaf r = true) := by
  let xs := Middle.sites s
  let bits := Middle.flags xs (Middle.occupied u)
  let common := Middle.flags xs (Middle.occupied t)
  let idx := Contacts.index orbitImages atlasPlanes
  let row (p : Port) := Middle.choices xs s t idx p.1 p.2
  let wins := (ports gaps cs).map row
  let fixed := wins.foldl (fun mask w => mask ||| w.scope) 0
  obtain ⟨ss,st⟩ := Middle.subBoth hs ht hu
  have sub : bits &&& common = bits := by
    unfold bits common
    rw [Middle.flags_and]
    apply Middle.flags_congr
    intro v _
    cases h : Middle.occupied u v
    · rfl
    · simp [(Middle.occupied_iff t v).mpr (st ((Middle.occupied_iff u v).mp h))]
  have hits : ∀ w ∈ wins, bits &&& w.scope ∈ w.picks := by
    intro w hw
    obtain ⟨⟨a,j⟩,hj,rfl⟩ := Array.mem_map.mp hw
    obtain ⟨a',_,he⟩ := Array.mem_flatMap.mp hj
    simp only [List.mem_toArray,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Middle.choice_contains atlas hc hs ht hu ss (full a).2
    · exact Middle.choice_contains atlas hc hs ht hu ss (full a).1
  have scope (i : Nat) (v : Middle.Site) (e : xs[i]? = some v) :
      fixed.testBit i = covered gaps cs v.word := by
    rw [show fixed = scopes ((ports gaps cs).toList.map row) 0 by
      simp only [fixed,wins,← Array.foldl_toList,Array.toList_map,scopes], scope_bit]
    simp only [Nat.zero_testBit,Bool.false_or,covered,Array.any_toList,Middle.Site.ofWord_word]
    congr 1
    funext p
    simp [row,Middle.choices,Middle.flags_bit,e]
  let vis := Middle.materialize xs (bits &&& fixed)
  have decode := decode_visible s u ss gaps cs fixed scope
  change cubeSet vis = (cubeSet u).filter _ at decode
  refine ⟨vis,hu ▸ decode,?_⟩
  intro pass
  let maxBits := (bits &&& fixed) ||| (common ^^^ (common &&& fixed))
  have decodeU := Middle.materialize_correct s u ss
  change cubeSet (Middle.materialize xs bits) = cubeSet u at decodeU
  have maxSub : cubeSet u ⊆ cubeSet (Middle.materialize xs maxBits) := by
    rw [← decodeU]
    apply materialize_mono
    intro i hb
    have hbit := congrArg (fun (a : Nat) => a.testBit i) sub
    have hcommon : common.testBit i = true := by simpa [Nat.testBit_and,hb] using hbit
    cases hf : fixed.testBit i <;> simp [maxBits,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hb,hcommon,hf]
  have low : ¬ 19 < Middle.count vis := by
    rw [Middle.count_eq,decode]
    exact Nat.not_lt.mpr ((Finset.card_le_card (Finset.filter_subset _ _)).trans hi)
  have high : ¬ Middle.count (Middle.materialize xs maxBits) < 16 :=
    Nat.not_lt.mpr (lo.trans ((Finset.card_le_card maxSub).trans_eq (Middle.count_eq _).symm))
  let terminal := fun n =>
    let r := Middle.materialize xs n
    decide (Middle.count r < 16) || decide (19 < Middle.count r) || leaf r
  let visit := fun f sel =>
    decide (19 < Middle.count (Middle.materialize xs sel)) ||
      decide (Middle.count (Middle.materialize xs (sel ||| (common ^^^ (common &&& f)))) < 16) ||
      !gate (Middle.materialize xs sel) || Middle.join common xs.size terminal #[] f sel
  have hw : walk common visit wins 0 (bits &&& 0) = true := by
    simp only [checked,Scan.prepare,Scan.getFn] at ok
    simpa only [Nat.and_zero] using ok
  have e := Middle.walkRows_sound common bits sub visit wins hits 0 hw
  change (decide (19 < Middle.count vis) || decide (Middle.count (Middle.materialize xs maxBits) < 16) ||
    !gate vis || Middle.join common xs.size terminal #[] fixed (bits &&& fixed)) = true at e
  simp only [decide_eq_false low,decide_eq_false high,pass,Bool.not_true,Bool.false_or] at e
  have h := Middle.join_sound common bits xs.size sub (Middle.flags_bound xs (Middle.occupied u)) terminal #[]
    (fun w h => False.elim (Array.not_mem_empty w h)) fixed e
  have pop := (Middle.count_eq (Middle.materialize xs bits)).trans (congrArg Finset.card decodeU)
  refine ⟨Middle.materialize xs bits,decodeU.trans hu,?_⟩
  simpa only [terminal,pop,decide_eq_false (Nat.not_lt.mpr lo),
    decide_eq_false (Nat.not_lt.mpr hi),Bool.false_or] using h

end SevenCycle.Adjacent.ScanFused
