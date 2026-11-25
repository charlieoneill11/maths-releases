import SevenCycle.Proof.Bitsets
import SevenCycleRuntime.Orbit
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin

/-!
# Enumerating the signed affine isometries on three coordinates

The 48 signed permutations are applied once each. Each resulting cube is
translated by cycling bits inside its planes and by moving the planes between
heights. Stabilizers may cause repeats in the output.
-/

namespace SevenCycle.Bitsets

open Proof (Tuple)


def perm3 (i : Fin 6) : Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)] i

theorem perm3_surjective : Function.Surjective perm3 := by
  have hi : Function.Injective perm3 := by
    have h : ∀ a b : Fin 6, perm3 a = perm3 b → a = b := by decide
    exact fun _ _ => h _ _
  have hc : Fintype.card (Fin 6) = Fintype.card (Equiv.Perm (Fin 3)) := by
    simp [Fintype.card_perm, Nat.factorial]
  exact (Fintype.bijective_iff_injective_and_card perm3).mpr ⟨hi, hc⟩ |>.2

def sign3 (i : Fin 8) (k : Fin 3) : Bool := i.val.testBit k.val

theorem sign3_surjective : ∀ f : Fin 3 → Bool, ∃ i : Fin 8, sign3 i = f := by decide

private def signedMotion (p : Fin 6) (s : Fin 8) : Isometry 3 :=
  (perm3 p, sign3 s, fun _ => 0)

private def translatePlane (p : Plane) (k : Fin 2) : Nat → Plane
  | 0 => p
  | n+1 => step (translatePlane p k n) k true

private theorem planeMem_translate (p : Plane) (k : Fin 2) (n : Nat) (w : Tuple 2) :
    planeMem (translatePlane p k n) w =
      planeMem p (fun j => if j = k then w j - (n : ZMod 7) else w j) := by
  induction n generalizing w with
  | zero => simp [translatePlane]
  | succ n ih =>
    rw [translatePlane, planeMem_step_plus, ih]
    congr 1
    ext j
    by_cases h : j = k <;> simp [h, sub_sub, add_comm]

private def translateLateral (c : Cube) (k : Fin 2) (v : Fin 7) : Cube :=
  c.map fun p => translatePlane p k v.val

private def translateHeight (c : Cube) (v : Fin 7) : Cube :=
  Vector.ofFn fun h : Fin 7 => c.get ((h : ZMod 7) - v)

private theorem native_move (p : Plane) (v : Nat) (b : Bool) :
    SevenCycleRuntime.Orbit.move b p v = translatePlane p (if b then 1 else 0) v := by
  induction v with
  | zero => rfl
  | succ v ih => cases b <;> simp only [translatePlane, SevenCycleRuntime.Orbit.move, ih] <;> rfl

private theorem native_lateral (c : Cube) (v : Fin 7) (b : Bool) :
    SevenCycleRuntime.Orbit.lateral c b v = translateLateral c (if b then 1 else 0) v := by
  simp [SevenCycleRuntime.Orbit.lateral, translateLateral, native_move]

private theorem native_height (c : Cube) (v : Fin 7) :
    SevenCycleRuntime.Orbit.rotateHeight c v = translateHeight c v := by
  have he : ∀ h v : Fin 7, Fin.ofNat 7 (h.val+7-v.val) = (h - v : ZMod 7) := by decide
  simp only [SevenCycleRuntime.Orbit.rotateHeight, translateHeight, he]

/-- Translations of one signed orientation. Each plane translation is shared
by all seven choices of shift in the height coordinate. -/
def translationImages (c : Cube) : Array Cube := SevenCycleRuntime.Orbit.translations c

private theorem contains_residue (i : Fin 7) : i ∈ Array.finRange 7 :=
  Array.mem_ofFn.mpr ⟨i,rfl⟩

private theorem translations_mem (c : Cube) (x y z : Fin 7) :
    translateHeight (translateLateral (translateLateral c 0 y) 1 z) x ∈ translationImages c := by
  simp only [translationImages, SevenCycleRuntime.Orbit.translations, native_height, native_lateral,
    Bool.false_eq_true, ↓reduceIte]
  exact Array.mem_flatMap.mpr ⟨y, contains_residue _, Array.mem_flatMap.mpr
    ⟨z, contains_residue _, Array.mem_map.mpr ⟨x, contains_residue _, rfl⟩⟩⟩

private theorem cubeMem_three_shifts (c : Cube) (v w : Tuple 3) :
    cubeMem (translateHeight (translateLateral (translateLateral c 0 (v 1)) 1 (v 2)) (v 0)) w =
      cubeMem c (fun i => w i - v i) := by
  change planeMem ((translateHeight _ _).get (w 0)) (Fin.tail w) =
    planeMem (c.get (w 0 - v 0)) (Fin.tail (fun i => w i - v i))
  simp only [translateHeight, translateLateral, Vector.get, Vector.ofFn, Array.getElem_ofFn,
    Vector.map, Array.getElem_map, planeMem_translate]
  congr 1
  ext j
  have hv (i : Fin 3) : ((v i).val : ZMod 7) = v i := ZMod.natCast_zmod_val _
  fin_cases j <;> simp [Fin.tail]
  · exact hv 1
  · exact hv 2

theorem translationImages_complete (v : Tuple 3) (c : Cube) :
    ∃ r ∈ translationImages c, cubeSet r =
      (cubeSet c).image (wordEquiv (Equiv.refl _, fun _ => false, v)) := by
  refine ⟨_, translations_mem c (v 0) (v 1) (v 2), ?_⟩
  rw [← cubeSet_act]
  ext w
  simp only [mem_cubeSet, cubeMem_three_shifts, cubeAct, cubeMem_buildCube]
  rfl


private def address (x : Tuple 3) : Fin 343 :=
  ⟨49*(x 0).val + 7*(x 1).val + (x 2).val, by
    have := ZMod.val_lt (x 0); have := ZMod.val_lt (x 1); have := ZMod.val_lt (x 2); omega⟩

private def point (j : Fin 343) : Tuple 3 :=
  ![↑(j.val/49), ↑(j.val/7%7), ↑(j.val%7)]

private theorem point_address : ∀ w : Tuple 3, point (address w) = w := by decide +kernel

private theorem read_address (c : Cube) (w : Tuple 3) :
    SevenCycleRuntime.Orbit.read c (address w) = cubeMem c w := by
  have key : ∀ x : Tuple 3, (address x).val/49 = (x 0).val ∧
      (address x).val%49 = 7*(x 1).val+(x 2).val := by decide +kernel
  obtain ⟨q,r⟩ := key w
  have eq : (⟨(address w).val/49, by have := (address w).isLt; omega⟩ : Fin 7) = w 0 := Fin.ext q
  simp only [SevenCycleRuntime.Orbit.read, eq, r, cubeMem]

private theorem lowBits_read (f : Nat → Bool) (n i : Nat) (hn : n ≤ 64) :
    (SevenCycleRuntime.Orbit.lowBits f n).toNat.testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [SevenCycleRuntime.Orbit.lowBits]
  | succ n ih =>
    have hn' : n < 64 := by omega
    have hpow : 2^n < 2^64 := Nat.pow_lt_pow_right (by decide) hn'
    cases h : f n <;> simp only [SevenCycleRuntime.Orbit.lowBits, h, Bool.false_eq_true, if_false, if_true,
      UInt64.toNat_or, Nat.testBit_or, ih (by omega), UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hpow, Nat.testBit_two_pow, UInt64.reduceToNat, Nat.zero_testBit,
      Bool.or_false] <;> rcases lt_trichotomy i n with hlt | rfl | hgt <;>
        simp_all [Nat.lt_succ_iff, Nat.le_of_lt, Nat.ne_of_lt, Nat.ne_of_gt, Nat.not_lt_of_le]

private def inverseAddresses (g : Isometry 3) : SevenCycleRuntime.Orbit.AddressMap :=
  Vector.ofFn fun j => address ((wordEquiv g).symm (point j))

private theorem orient_mem (g : Isometry 3) (c : Cube) (w : Tuple 3) :
    cubeMem (SevenCycleRuntime.Orbit.orient c (inverseAddresses g)) w = cubeMem c ((wordEquiv g).symm w) := by
  have h : 7 * (w 1).val + (w 2).val < 49 := by
    have := ZMod.val_lt (w 1); have := ZMod.val_lt (w 2); omega
  have addr : Fin.ofNat 343 (49*(w 0).val + (7*(w 1).val + (w 2).val)) = address w := by
    apply Fin.ext
    simp only [Fin.val_ofNat, address]
    rw [← Nat.add_assoc]
    exact Nat.mod_eq_of_lt (address w).isLt
  simp only [cubeMem, SevenCycleRuntime.Orbit.orient, Vector.get, Vector.ofFn, Array.getElem_ofFn,
    lowBits_read _ 49 _ (by decide), decide_eq_true h, Bool.true_and]
  change SevenCycleRuntime.Orbit.read c ((inverseAddresses g).get
    (Fin.ofNat 343 (49*(w 0).val + (7*(w 1).val + (w 2).val)))) = _
  rw [addr]
  have getFn {n : Nat} (f : Fin n → Fin 343) (j : Fin n) : (Vector.ofFn f).get j = f j := by
    change (Vector.ofFn f)[j.val] = f j
    rw [Vector.getElem_ofFn]
  have table (j : Fin 343) : (inverseAddresses g).get j = address ((wordEquiv g).symm (point j)) :=
    getFn _ _
  rw [table, point_address, read_address]
  rfl

def motionTable : Array SevenCycleRuntime.Orbit.AddressMap :=
  (Array.finRange 6).flatMap fun p =>
    (Array.finRange 8).map fun s => inverseAddresses (signedMotion p s)

/-- All 16,464 motions, counting stabilizer multiplicities. -/
def orbitImages (c : Cube) : Array Cube := SevenCycleRuntime.Orbit.images motionTable c

/-- Every labelled isometric image of the input cube occurs in the array. -/
theorem orbitImages_complete (g : Isometry 3) (c : Cube) :
    ∃ r ∈ orbitImages c, cubeSet r = (cubeSet c).image (wordEquiv g) := by
  obtain ⟨p, hp⟩ := perm3_surjective g.1
  obtain ⟨s, hs⟩ := sign3_surjective g.2.1
  let signed := SevenCycleRuntime.Orbit.orient c (inverseAddresses (signedMotion p s))
  let t := g.2.2
  have hmv : inverseAddresses (signedMotion p s) ∈ motionTable :=
    Array.mem_flatMap.mpr ⟨p, Array.mem_ofFn.mpr ⟨p,rfl⟩, Array.mem_map.mpr
      ⟨s, Array.mem_ofFn.mpr ⟨s,rfl⟩, rfl⟩⟩
  refine ⟨_, Array.mem_flatMap.mpr ⟨_, hmv, translations_mem signed (t 0) (t 1) (t 2)⟩, ?_⟩
  rw [← cubeSet_act]
  ext w
  simp only [mem_cubeSet, cubeMem_three_shifts, signed, orient_mem, cubeAct, cubeMem_buildCube]
  simp [signedMotion, hp, hs, wordEquiv, t]

end SevenCycle.Bitsets
