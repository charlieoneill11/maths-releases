import SevenCycle.Adjacent.Support
import SevenCycle.Proof.Deficits

/-! Dynamic-programming upper bounds for completing the rows of a transverse window. -/

namespace SevenCycle.Atlas.WindowDP

open Proof Bitsets

abbrev Row := Fin 128

@[inline] private def has (r : Row) (i : Fin 7) := r.val.testBit i.val
private def cells (r : Row) : Finset (ZMod 7) := Finset.univ.filter fun i : ZMod 7 => has r i = true

private def rows : Array Row := Array.finRange 128
private def coords : Array (Fin 7) := Array.finRange 7

@[inline] private def close (x y : Fin 7) : Bool :=
  x == y || x+1 == y || y+1 == x

private theorem close_iff : ∀ x y : Fin 7, close x y = true ↔ cycleStep x y := by
  unfold cycleStep
  decide

private def allowed (r : Row) : Bool := coords.all fun x =>
  coords.all fun y => !(has r x && has r y && (x != y) && close x y)

private def follows (r s : Row) : Bool := coords.all fun x =>
  coords.all fun y => !(has r x && has s y && close x y)

private theorem allowed_of (r : Row) (h : ∀ x ∈ cells r, ∀ y ∈ cells r, x ≠ y → ¬ cycleStep x y) :
    allowed r = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro x hx
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro y hy
  cases hp : has r x <;> cases hq : has r y <;> simp
  by_cases hne : x = y
  · exact Or.inl hne
  apply Or.inr
  exact Bool.eq_false_iff.mpr (fun hc => h _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩) hne ((close_iff ..).mp hc))

private theorem follows_of (r s : Row) (h : ∀ x ∈ cells r, ∀ y ∈ cells s, ¬ cycleStep x y) :
    follows r s = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro x hx
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro y hy
  cases hp : has r x <;> cases hq : has s y <;> simp
  exact Bool.eq_false_iff.mpr (fun hc => h _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩) ((close_iff ..).mp hc))

private def nextRows : Vector (Array Row) 128 := Vector.ofFn fun b =>
  rows.filter fun r => allowed r && follows b r

set_option maxRecDepth 10000 in
private theorem next_mem (b r : Row) (ha : allowed r = true) (hf : follows b r = true) :
    r ∈ nextRows[b.val] := by
  simp only [nextRows, Vector.getElem_ofFn, Array.mem_filter, ha, hf, Bool.and_self, and_true]
  change r ∈ Array.finRange 128
  exact Array.mem_ofFn.mpr ⟨r, rfl⟩

private def weights : Vector Nat 128 := Vector.ofFn fun r => (coords.filter (has r)).size

set_option maxRecDepth 10000 in
private theorem weight_eq (r : Row) : weights[r.val] = (cells r).card := by
  revert r
  decide +kernel

private def ix (a b : Row) : Fin 16384 := ⟨128*a.val+b.val, by have := a.isLt; have := b.isLt; omega⟩
private def left (i : Fin 16384) : Row := ⟨i.val/128, by have := i.isLt; omega⟩
private def right (i : Fin 16384) : Row := ⟨i.val%128, Nat.mod_lt _ (by decide)⟩

private theorem left_ix (a b : Row) : left (ix a b) = a := by
  apply Fin.ext
  change (128*a.val+b.val)/128 = a.val
  have := b.isLt; omega

private theorem right_ix (a b : Row) : right (ix a b) = b := by
  apply Fin.ext
  change (128*a.val+b.val)%128 = b.val
  have := b.isLt; omega

private def advance (prev : Vector Nat 16384) (a b : Row) : Nat :=
  (nextRows[b.val]).foldl (fun best r =>
    let w := prev[(ix a r).val]
    if w = 0 then best else max best (weights[r.val] + w)) 0

private def layer : Nat → Vector Nat 16384
  | 0 => Vector.ofFn fun i => if follows (right i) (left i) then 1 else 0
  | n+1 =>
    let prev := layer n
    Vector.ofFn fun i => advance prev (left i) (right i)

private def allLayers : Vector (Vector Nat 16384) 7 := Vector.ofFn fun n => layer n.val

private theorem advance_ge (prev : Vector Nat 16384) (a b r : Row) (hr : r ∈ nextRows[b.val])
    (hp : 0 < prev[(ix a r).val]) : weights[r.val] + prev[(ix a r).val] ≤ advance prev a b := by
  let update (best : Nat) (s : Row) :=
    if prev[(ix a s).val] = 0 then best else max best (weights[s.val] + prev[(ix a s).val])
  have go (xs : List Row) (acc : Nat) :
      acc ≤ xs.foldl update acc ∧ (r ∈ xs → weights[r.val] + prev[(ix a r).val] ≤ xs.foldl update acc) := by
    induction xs generalizing acc with
    | nil => simp
    | cons s xs ih =>
      have h := ih (update acc s)
      have hinc : acc ≤ update acc s := by unfold update; split <;> simp
      refine ⟨hinc.trans h.1, ?_⟩
      intro hmem
      rcases List.mem_cons.mp hmem with he | hmem
      · subst s
        exact (show weights[r.val] + prev[(ix a r).val] ≤ update acc r by
          simp [update, Nat.ne_of_gt hp]).trans h.1
      · exact h.2 hmem
  simpa only [advance, ← Array.foldl_toList] using (go (nextRows[b.val]).toList 0).2 (by simpa using hr)

/-- A legal ordered path of intermediate rows, closed against the first row.
The accumulator counts only the added rows, excluding the fixed endpoints. -/
private inductive Path (first : Row) : Nat → Row → Nat → Prop
  | close (b : Row) (ok : follows b first = true) : Path first 0 b 0
  | step {n count : Nat} {b r : Row} (allow : allowed r = true) (ok : follows b r = true)
      (tail : Path first n r count) : Path first (n+1) b ((cells r).card + count)

private theorem path_bound {n size : Nat} {first last : Row} (h : Path first n last size) :
    size+1 ≤ (layer n)[(ix first last).val] := by
  induction h with
  | close b ok => simp [layer, left_ix, right_ix, ok]
  | @step n count b r allow ok tail ih =>
    have pos : 0 < (layer n)[(ix first r).val] := by omega
    have h := advance_ge (layer n) first b r (next_mem b r allow ok) pos
    simp only [layer, Vector.getElem_ofFn]
    change (cells r).card + count + 1 ≤ advance (layer n) (left (ix first b)) (right (ix first b))
    rw [left_ix, right_ix]
    rw [weight_eq] at h
    omega

@[inline] private def readRow (p : Plane) (i : ZMod 7) : Row :=
  ⟨(p >>> (7*i.val).toUInt64).toNat % 128, Nat.mod_lt _ (by decide)⟩

private theorem mem_readRow (p : Plane) (i z : ZMod 7) :
    z ∈ cells (readRow p i) ↔ ![i,z] ∈ planeSet p := by
  have hshift : ∀ i : ZMod 7, (7*i.val).toUInt64.toNat % 64 = 7*i.val := by decide
  simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and, has, readRow, mem_planeSet,
    planeMem, index, UInt64.toNat_shiftRight, hshift i]
  change ((p.toNat >>> (7*i.val)) % 2^7).testBit z.val = true ↔ _
  have hz : z.val < 7 := z.isLt
  rw [Nat.testBit_mod_two_pow, decide_eq_true hz, Bool.true_and, Nat.testBit_shiftRight]
  rfl

private theorem row_eq {r s : Row} (hc : cells r = cells s) : r = s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 7
  · have h := Finset.ext_iff.mp hc (⟨i, hi⟩ : Fin 7)
    simpa only [cells, Finset.mem_filter, Finset.mem_univ, true_and, has, Bool.coe_iff_coe] using h
  · have hpow : 128 ≤ 2^i := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show 7 ≤ i by omega)
    rw [Nat.testBit_lt_two_pow (r.isLt.trans_le hpow), Nat.testBit_lt_two_pow (s.isLt.trans_le hpow)]

private theorem maskPopulation (p : Plane) :
    (planeSet p).card = ∑ i : ZMod 7, (cells (readRow p i)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Tuple 2 => x 0)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _
  refine Finset.card_bij' (fun x _ => x 1) (fun z _ => ![i,z]) ?_ ?_ ?_ ?_
  · intro x hx
    change x 1 ∈ cells (readRow p i)
    rw [mem_readRow]
    have he : ![i,x 1] = x := by
      rw [← (Finset.mem_filter.mp hx).2]
      funext j
      fin_cases j <;> rfl
    rw [he]
    exact (Finset.mem_filter.mp hx).1
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(mem_readRow ..).mp hz, rfl⟩
  · intro x hx
    change ![i, x 1] = x
    rw [← (Finset.mem_filter.mp hx).2]
    funext j
    fin_cases j <;> rfl
  · intros; rfl

private def tailCount (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, j => f (j+1) + tailCount f n (j+1)

private theorem buildPath (F : Nat → Row) (ok : ∀ i, allowed (F i) = true)
    (edges : ∀ i, follows (F i) (F (i+1)) = true) (n j : Nat) :
    Path (F (j+n+1)) n (F j) (tailCount (fun i => (cells (F i)).card) n j) := by
  induction n generalizing j with
  | zero => exact Path.close _ (edges _)
  | succ n ih =>
    have hrec := ih (j+1)
    rw [show j+1+n+1 = j+(n+1)+1 by omega] at hrec
    exact Path.step (ok _) (edges _) hrec

private theorem partition (f : ZMod 7 → Nat) (j : Fin 7) :
    ∑ i, f i = (∑ i : ZMod 7, if i.val ≤ j.val then f i else 0) +
      tailCount (fun i => f (i : ZMod 7)) (6-j.val) j.val := by
  rw [Deficits.sum_seven_at f 0, Deficits.sum_seven_at (fun i => if i.val ≤ j.val then f i else 0) 0]
  simp only [zero_add]
  fin_cases j
  · change _ = (f 0 + (0 + (0 + (0 + (0 + (0 + 0)))))) + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + 0))))))
    omega
  · change _ = (f 0 + (f 1 + (0 + (0 + (0 + (0 + 0)))))) + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + 0)))))
    omega
  · change _ = (f 0 + (f 1 + (f 2 + (0 + (0 + (0 + 0)))))) + (f 3 + (f 4 + (f 5 + (f 6 + 0))))
    omega
  · change _ = (f 0 + (f 1 + (f 2 + (f 3 + (0 + (0 + 0)))))) + (f 4 + (f 5 + (f 6 + 0)))
    omega
  · change _ = (f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (0 + 0)))))) + (f 5 + (f 6 + 0))
    omega
  · change _ = (f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + 0)))))) + (f 6 + 0)
    omega
  · change _ = (f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + f 6)))))) + 0
    omega

/-- The seven completed dynamic-programming layers, exposed to the compiled search. -/
def completionBounds : Vector (Vector Nat 16384) 7 := allLayers

/-- Maximum possible total population of a completed planar window, from a
prefix through row j. A zero table entry means no legal closure is possible. -/
@[inline] def prefixBound (j : Fin 7) (p : Plane) : Nat :=
  let n : Fin 7 := ⟨6-j.val, by omega⟩
  let bound := (allLayers[n.val])[(ix (readRow p 0) (readRow p j)).val]
  if bound = 0 then 0 else Adjacent.maskCard p + (bound-1)

theorem prefixBound_sound (D : Finset (Tuple 2)) (hc : packing cycleStep D)
    (j : Fin 7) (p : Plane) (hp : planeSet p = D.filter (fun w => (w 0).val ≤ j.val)) :
    D.card ≤ prefixBound j p := by
  let full := buildPlane fun w => decide (w ∈ D)
  have hfull : planeSet full = D := by ext w; simp [full]
  let F := fun i : ZMod 7 => readRow full i
  have memF (i y : ZMod 7) : y ∈ cells (F i) ↔ ![i,y] ∈ D := by rw [← hfull]; exact mem_readRow ..
  have valid (i : ZMod 7) : allowed (F i) = true := by
    apply allowed_of
    intro x hx y hy hne hclose
    apply hc _ ((memF i x).mp hx) _ ((memF i y).mp hy)
    refine ⟨fun e => hne (congrFun e 1), ?_⟩
    intro u
    fin_cases u
    · simp [cycleStep]
    · exact hclose
  have neighbors (i : ZMod 7) : follows (F i) (F (i+1)) = true := by
    apply follows_of
    intro x hx y hy hclose
    apply hc _ ((memF i x).mp hx) _ ((memF (i+1) y).mp hy)
    have ha : ∀ i : ZMod 7, i ≠ i+1 ∧ cycleStep i (i+1) := by unfold cycleStep; decide
    refine ⟨fun e => (ha i).1 (congrFun e 0), ?_⟩
    intro u
    fin_cases u
    · exact (ha i).2
    · exact hclose
  have hpath := buildPath (fun i : Nat => F (i : ZMod 7)) (fun _ => valid _)
    (fun i => by simpa using neighbors (i : ZMod 7)) (6-j.val) j.val
  rw [show j.val+(6-j.val)+1 = 7 by have := j.isLt; omega] at hpath
  have he : ∀ i : ZMod 7, cells (readRow p i) = if i.val ≤ j.val then cells (F i) else ∅ := by
    intro i
    ext y
    by_cases h : i.val ≤ j.val <;> simp [h, memF, mem_readRow, hp]
  have same (i : ZMod 7) (hi : i.val ≤ j.val) : readRow p i = F i :=
    row_eq (by simpa [hi] using he i)
  have anchor := same 0 (by exact Nat.zero_le _)
  have last := same j (by exact Nat.le_refl _)
  let value := (layer (6-j.val))[(ix (F 0) (F j)).val]
  have bound : tailCount (fun n => (cells (F (n : ZMod 7))).card) (6-j.val) j.val + 1 ≤ value := by
    have h := path_bound hpath
    have asZ : ∀ k : Fin 7, (k.val : ZMod 7) = k := by decide
    have jcast := asZ j
    simpa only [jcast, Nat.cast_ofNat, show (7 : ZMod 7) = 0 by decide]
      using h
  have cardPrefix : planeCard p = ∑ i : ZMod 7, if i.val ≤ j.val then (cells (F i)).card else 0 := by
    rw [planeCard_eq, maskPopulation]
    apply Finset.sum_congr rfl
    intro i _
    rw [he]
    split <;> simp
  have count := partition (fun i => (cells (F i)).card) j
  rw [← cardPrefix] at count
  have total : D.card = ∑ i : ZMod 7, (cells (F i)).card := hfull ▸ maskPopulation full
  rw [← total] at count
  unfold prefixBound
  simp only [allLayers, Vector.getElem_ofFn, anchor, last, Adjacent.maskCard_eq]
  change D.card ≤ if value = 0 then 0 else planeCard p + (value-1)
  rw [if_neg (by omega)]
  omega

end SevenCycle.Atlas.WindowDP
