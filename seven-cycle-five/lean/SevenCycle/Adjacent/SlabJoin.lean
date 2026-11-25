import SevenCycle.Blueprint.Definitions
import SevenCycleRuntime.SlabJoin
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-!
# Joining four adjacent slabs

A slab is stored as the 2,401 bits of its occupied sites in base-seven order.
Hash buckets index the three independent overlap constraints for the last
slab. Equal masks always have equal keys, so a collision only adds candidates.
-/

namespace SevenCycle.Adjacent.SlabJoin

open Blueprint Proof

def address (x : Tuple 4) : Nat :=
  343*(x 0).val + 49*(x 1).val + 7*(x 2).val + (x 3).val

def position (j : Nat) : Tuple 4 :=
  ![(j / 343 : Nat), (j / 49 % 7 : Nat), (j / 7 % 7 : Nat), (j % 7 : Nat)]

/-- All bits, including those beyond the torus, are specified. -/
def Stores (bits : Nat) (C : Finset (Tuple 4)) : Prop :=
  ∀ j, bits.testBit j = true ↔ j < 2401 ∧ position j ∈ C

def inThree (k : Fin 4) (x : Tuple 4) : Prop := x k = 6 ∨ x k = 0 ∨ x k = 1

instance (k : Fin 4) (x : Tuple 4) : Decidable (inThree k x) := by
  unfold inThree
  infer_instance

theorem maskUpTo_bit (p : Nat → Bool) (n i : Nat) :
    (maskUpTo p n).testBit i = (decide (i < n) && p i) := by
  induction n with
  | zero => simp [maskUpTo]
  | succ n ih =>
    simp only [maskUpTo, Nat.testBit_or, ih, Nat.one_shiftLeft]
    by_cases hp : p n = true
    · rw [if_pos hp, Nat.testBit_two_pow]
      rcases lt_trichotomy i n with lt | rfl | gt
      · simp [lt, lt_trans lt (Nat.lt_succ_self n), Nat.ne_of_gt lt]
      · simp [hp]
      · simp [Nat.not_lt.mpr (Nat.le_of_lt gt), Nat.not_lt.mpr gt, Nat.ne_of_lt gt]
    · rw [if_neg hp, Nat.zero_testBit, Bool.or_false]
      by_cases he : n = i
      · subst i; simp [Bool.eq_false_of_not_eq_true hp]
      · have hiff : i < n+1 ↔ i < n := by omega
        simp only [hiff]

def region (k : Fin 4) : Nat := maskUpTo (fun j => decide (inThree k (position j))) 2401

private theorem region_bit (k : Fin 4) (j : Nat) :
    (region k).testBit j = true ↔ j < 2401 ∧ inThree k (position j) := by
  simp [region, maskUpTo_bit]

@[inline] def key (r : Nat) (k : Fin 4) : UInt64 :=
  ((r &&& region k) % 18446744073709551557).toUInt64

theorem keys_agree {C : Finset (Tuple 4)} {a b : Fin 4} {s t : Nat}
    (hs : Stores s (C.filter (inThree a))) (ht : Stores t (C.filter (inThree b))) :
    key s b = key t a := by
  have h : s &&& region b = t &&& region a := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    simp only [Nat.testBit_and, Bool.and_eq_true, hs i, ht i, region_bit, Finset.mem_filter]
    tauto
  rw [key, key, h]

def ofBits (bits : Nat) : Slab := ⟨bits,key bits 0,key bits 1,key bits 2,key bits 3⟩

theorem indexBy_covers {α β : Type} [BEq α] [LawfulBEq α] [Hashable α]
    (rows : Array β) (f : β → α) {r : β} (hr : r ∈ rows) :
    r ∈ (indexBy rows f).getD (f r) #[] := by
  classical
  let add := fun (m : Std.HashMap α (Array β)) (u : β) =>
    m.alter (f u) fun old => some ((old.getD #[]).push u)
  have lookup (m : Std.HashMap α (Array β)) (u : β) (z : α) :
      (add m u).getD z #[] =
        if f u = z then (m.getD z #[]).push u else m.getD z #[] := by
    by_cases h : f u = z <;> simp [add, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_alter, h]
  have hh := Array.foldl_induction (as := rows) (f := add) (init := ({} : Std.HashMap α (Array β)))
    (motive := fun n (m : Std.HashMap α (Array β)) => ∀ i : Fin rows.size, i.val < n → rows[i] ∈ m.getD (f rows[i]) #[])
    (by intro i hi; omega) (by
      intro i m ih j hj
      rw [lookup]
      by_cases eq : i = j
      · subst j; simp
      · have lt : j.val < i.val := by
          have : j.val ≠ i.val := fun h => eq (Fin.ext h.symm)
          omega
        split
        · exact Array.mem_push.mpr (.inl (ih j lt))
        · exact ih j lt)
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
  exact hh ⟨i, hi⟩ hi

theorem checkJoin_sound {a b c d : Array Slab} {leaf : Nat → Bool}
    (h : checkJoin a b c d leaf = true) {C : Finset (Tuple 4)} (bits : Fin 4 → Nat)
    (hbits : ∀ k, Stores (bits k) (C.filter (inThree k)))
    (ha : ofBits (bits 0) ∈ a) (hb : ofBits (bits 1) ∈ b)
    (hc : ofBits (bits 2) ∈ c) (hd : ofBits (bits 3) ∈ d) :
    leaf (bits 0 ||| bits 1 ||| bits 2 ||| bits 3) = true := by
  let ka := fun (i j : Fin 4) => keys_agree (hbits i) (hbits j)
  have hinb := indexBy_covers b Slab.k0 hb
  have hinc := indexBy_covers c (fun r => (r.k0,r.k1)) hc
  have hind := indexBy_covers d (fun r => (r.k0,r.k1,r.k2)) hd
  simp only [ofBits] at hinb hinc hind
  rw [ka 1 0] at hinb
  rw [ka 2 0, ka 2 1] at hinc
  rw [ka 3 0, ka 3 1, ka 3 2] at hind
  exact Array.all_eq_true'.mp (Array.all_eq_true'.mp (Array.all_eq_true'.mp
    (Array.all_eq_true'.mp h _ ha) _ hinb) _ hinc) _ hind


def Includes (d : Domains) (r : Fin 4 → Slab) : Prop := ∀ k, r k ∈ d[k]

private theorem lookupKey {d : Array Slab} {r : Slab} (h : r ∈ d) (k : Fin 4) :
    faceKey r k ∈ d.foldl (init := ({} : Std.HashSet UInt64)) (fun seen u => seen.insert (faceKey u k)) := by
  have all := Array.foldl_induction (as := d)
    (f := fun (seen : Std.HashSet UInt64) (u : Slab) => seen.insert (faceKey u k))
    (init := ({} : Std.HashSet UInt64))
    (motive := fun n (m : Std.HashSet UInt64) => ∀ i : Fin d.size, i.val < n → faceKey d[i] k ∈ m)
    (by intro i hi; omega) (by
      intro i m ih j hj
      by_cases eq : i = j
      · subst j; simp
      · have lt : j.val < i.val := by
          have : j.val ≠ i.val := fun e => eq (Fin.ext e.symm)
          omega
        exact Std.HashSet.mem_insert.mpr (Or.inr (ih j lt)))
  obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp h
  exact all ⟨i,hi⟩ hi

private theorem pruneStep_retains {d : Domains} {r : Fin 4 → Slab} (hd : Includes d r)
    (agree : ∀ a b, faceKey (r a) b = faceKey (r b) a) (a b : Fin 4) :
    Includes (pruneStep d a b) r := by
  unfold pruneStep
  split
  · exact hd
  · intro k
    change r k ∈ (d.set a.val _)[k.val]
    by_cases hk : a = k
    · subst k
      simp only [Vector.getElem_set_self, Array.mem_filter, Std.HashSet.contains_iff_mem]
      exact ⟨hd a, (agree a b).symm ▸ lookupKey (hd b) a⟩
    · rw [Vector.getElem_set_ne (h := fun h => hk (Fin.ext h))]
      exact hd k

theorem prune_retains {r : Fin 4 → Slab} (agree : ∀ a b, faceKey (r a) b = faceKey (r b) a)
    (n : Nat) (d : Domains) (h : Includes d r) : Includes (prune n d) r := by
  induction n generalizing d with
  | zero => exact h
  | succ n ih =>
    apply ih
    unfold prunePass
    apply Array.foldl_induction (motive := fun _ s => Includes s r) h
    intro a s hs
    apply Array.foldl_induction (motive := fun _ s => Includes s r) hs
    intro b t ht
    exact pruneStep_retains ht agree _ _

theorem actual_keys {C : Finset (Tuple 4)} (bits : Fin 4 → Nat)
    (h : ∀ k, Stores (bits k) (C.filter (inThree k))) (i j : Fin 4) :
    faceKey (ofBits (bits i)) j = faceKey (ofBits (bits j)) i := by
  have hk (n : Nat) (k : Fin 4) : faceKey (ofBits n) k = key n k := by fin_cases k <;> rfl
  exact (hk _ _).trans ((keys_agree (h i) (h j)).trans (hk _ _).symm)


theorem address_position : ∀ i : Fin 2401, address (position i.val) = i.val := by
  intro i
  simp [address, position, ZMod.val_natCast]
  omega
theorem coords_position : ∀ (i : Fin 2401) (k : Fin 4), coords i.val k = (position i.val k).val := by
  intro i k
  fin_cases k <;> simp [coords, position, ZMod.val_natCast]
  omega

private theorem consecutive_sound : ∀ a b : ZMod 7, consecutive a.val b.val → cycleStep a b := by
  unfold cycleStep
  decide

private theorem conflictIDs_sound {p q : Nat} (hp : p < 2401) (hq : q < 2401)
    (h : conflictIDs p q = true) : conflict cycleStep (position p) (position q) := by
  simp only [conflictIDs, Bool.and_eq_true, bne_iff_ne] at h
  refine ⟨fun eq => h.1.1.1.1 ((address_position ⟨p,hp⟩).symm.trans
    ((congrArg address eq).trans (address_position ⟨q,hq⟩))), ?_⟩
  intro k
  apply consecutive_sound
  rw [← coords_position ⟨p,hp⟩ k, ← coords_position ⟨q,hq⟩ k]
  fin_cases k
  · exact h.1.1.1.2
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

private theorem blocks_witness (table : Array Nat) (bits j : Nat)
    (h : (blocksFrom table bits).testBit j = true) :
    ∃ i, bits.testBit i = true ∧ (table[i]?.getD 0).testBit j = true := by
  have all := Array.foldl_induction (as := Array.range 2401)
    (f := fun (b i : Nat) => if bits.testBit i then b ||| (table[i]?.getD 0) else b)
    (init := 0) (motive := fun _ b => b.testBit j = true →
        ∃ i, bits.testBit i = true ∧ (table[i]?.getD 0).testBit j = true)
    (by simp) (by
      intro i b ih
      dsimp only
      split
      · rename_i hn
        rw [Nat.testBit_or, Bool.or_eq_true]
        exact fun e => e.elim ih (fun x => ⟨_,hn,x⟩)
      · exact ih)
  exact all h

theorem clear_of_code {C : Finset (Tuple 4)} (hc : packing cycleStep C)
    {a b : Fin 4} {s t : Nat} (hs : Stores s (C.filter (inThree a)))
    (ht : Stores t (C.filter (inThree b))) : t &&& blocksFrom neighborTable s = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_contra h
  have hh := Bool.and_eq_true_iff.mp (Bool.eq_true_of_not_eq_false h)
  obtain ⟨hj,hy⟩ := (ht j).mp hh.1
  obtain ⟨i,hi,hmask⟩ := blocks_witness _ _ _ hh.2
  obtain ⟨hir,hx⟩ := (hs i).mp hi
  have atRow : neighborTable[i]? = some (maskUpTo (conflictIDs i) 2401) := by
    simp [neighborTable, hir]
  rw [atRow] at hmask
  have hcids := (Bool.and_eq_true_iff.mp ((maskUpTo_bit _ _ _).symm ▸ hmask)).2
  exact hc _ (Finset.mem_filter.mp hx).1 _ (Finset.mem_filter.mp hy).1
    (conflictIDs_sound hir hj hcids)

attribute [local irreducible] blocksFrom neighborTable

theorem checkSlabs_sound {C : Finset (Tuple 4)} (hc : packing cycleStep C)
    (d : Domains) (bits : Fin 4 → Nat) (h : ∀ k, Stores (bits k) (C.filter (inThree k)))
    (hd : Includes d (fun i => ofBits (bits i))) {leaf : Nat → Bool}
    (ok : checkSlabs d neighborTable leaf = true) :
    leaf (bits 0 ||| bits 1 ||| bits 2 ||| bits 3) = true := by
  let raw := prune 4 d
  let x := raw.map (·.map (active neighborTable))
  let r := fun i => active neighborTable (ofBits (bits i))
  have hp := prune_retains (actual_keys bits h) 4 d hd
  have mem (i : Fin 4) : r i ∈ x[i] := by
    change r i ∈ (raw.map (·.map (active neighborTable)))[i.val]
    simp only [Vector.getElem_map]
    exact Array.mem_map_of_mem (hp i)
  have hb := indexBy_covers x[1] (fun v => v.slab.k0) (mem 1)
  have hcc := indexBy_covers x[2] (fun v => (v.slab.k0,v.slab.k1)) (mem 2)
  have hd' := indexBy_covers x[3] (fun v => (v.slab.k0,v.slab.k1,v.slab.k2)) (mem 3)
  simp only [r, active, ofBits] at hb hcc hd'
  rw [keys_agree (h 1) (h 0)] at hb
  rw [keys_agree (h 2) (h 0), keys_agree (h 2) (h 1)] at hcc
  rw [keys_agree (h 3) (h 0), keys_agree (h 3) (h 1), keys_agree (h 3) (h 2)] at hd'
  have b_ok := Array.all_eq_true'.mp (Array.all_eq_true'.mp ok _ (mem 0)) _ hb
  have zero (b a : Fin 4) : bits b &&& blocksFrom neighborTable (bits a) = 0 :=
    clear_of_code hc (h a) (h b)
  have pair : (r 1).slab.bits &&& (r 0).ban = 0 := by
    simpa only [r, active, ofBits] using zero 1 0
  have triple : (r 2).slab.bits &&& ((r 0).ban ||| (r 1).ban) = 0 := by
    change bits 2 &&& (blocksFrom neighborTable (bits 0) ||| blocksFrom neighborTable (bits 1)) = 0
    rw [Nat.and_or_distrib_left, zero 2 0, zero 2 1, Nat.zero_or]
  have quad : (r 3).slab.bits &&& ((r 0).ban ||| (r 1).ban ||| (r 2).ban) = 0 := by
    simp only [r, active, ofBits]
    rw [Nat.and_or_distrib_left, Nat.and_or_distrib_left, zero 3 0, zero 3 1, zero 3 2,
      Nat.zero_or, Nat.zero_or]
  have keep {n : Nat} {b : Bool} (z : n = 0) (ok : ((n != 0) || b) = true) : b = true := by
    simpa only [z, bne_self_eq_false, Bool.false_or] using ok
  have c_ok := Array.all_eq_true'.mp (keep pair b_ok) _ hcc
  have d_ok := Array.all_eq_true'.mp (keep triple c_ok) _ hd'
  exact keep quad d_ok

end SevenCycle.Adjacent.SlabJoin
