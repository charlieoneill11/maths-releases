import SevenCycle.Proof.Model
import Mathlib.Data.Fin.VecNotation

/-! Packed subsets in the plane and in the cube. At height `x` the point
`(x,y,z)` has bit index `7*y+z`. Mathematical interpretations ignore the
unused fifteen high bits. Rebuilding a plane always clears them. -/

namespace SevenCycle.Bitsets

open Proof (Tuple cycleStep)

abbrev Plane := UInt64
abbrev Cube := Vector UInt64 7

@[inline] def index (w : Tuple 2) : Nat := 7 * (w 0).val + (w 1).val

@[inline] def pointAt (i : Nat) : Tuple 2 := ![((i / 7 : Nat) : ZMod 7), ((i % 7 : Nat) : ZMod 7)]

theorem index_lt : ∀ x : Tuple 2, index x < 49 := by decide

@[simp] theorem pointAt_index : ∀ x : Tuple 2, pointAt (index x) = x := by decide

@[simp] theorem index_pointAt : ∀ i : Fin 49, index (pointAt i) = i.val := by decide

@[inline] def planeMem (p : Plane) (x : Tuple 2) : Bool := p.toNat.testBit (index x)

@[inline] def cubeMem (c : Cube) (w : Tuple 3) : Bool :=
  (c.get (w 0)).toNat.testBit (7 * (w 1).val + (w 2).val)

def planeSet (p : Plane) : Finset (Tuple 2) := Finset.univ.filter (planeMem p ·)

def cubeSet (c : Cube) : Finset (Tuple 3) := Finset.univ.filter (cubeMem c ·)

@[simp] theorem mem_planeSet (p : Plane) (x : Tuple 2) : x ∈ planeSet p ↔ planeMem p x := by
  simp [planeSet]

@[simp] theorem mem_cubeSet (c : Cube) (x : Tuple 3) : x ∈ cubeSet c ↔ cubeMem c x := by
  simp [cubeSet]

/-- Set the low `n` bits from the predicate. All uses have `n ≤ 49`. -/
private def lowBits (f : Nat → Bool) : Nat → UInt64
  | 0 => 0
  | n+1 => lowBits f n ||| (if f n then UInt64.ofNat (2 ^ n) else 0)

private theorem test_lowBits (f : Nat → Bool) (n i : Nat) (hn : n ≤ 64) :
    (lowBits f n).toNat.testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [lowBits]
  | succ n ih =>
    have hn' : n < 64 := by omega
    have hpow : 2^n < 2^64 := Nat.pow_lt_pow_right (by decide) hn'
    cases h : f n <;> simp only [lowBits, h, Bool.false_eq_true, if_false, if_true,
      UInt64.toNat_or, Nat.testBit_or, ih (by omega), UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hpow, Nat.testBit_two_pow, UInt64.reduceToNat, Nat.zero_testBit,
      Bool.or_false] <;> rcases lt_trichotomy i n with hlt | rfl | hgt <;>
        simp_all [Nat.lt_succ_iff, Nat.le_of_lt, Nat.ne_of_lt, Nat.ne_of_gt, Nat.not_le_of_lt, Nat.not_lt_of_ge]

def buildPlane (f : Tuple 2 → Bool) : Plane := lowBits (fun i => f (pointAt i)) 49

@[simp] theorem planeMem_buildPlane (f : Tuple 2 → Bool) (x : Tuple 2) :
    planeMem (buildPlane f) x = f x := by
  simp [planeMem, buildPlane, test_lowBits _ 49 _ (by decide), index_lt]

def buildCube (f : Tuple 3 → Bool) : Cube :=
  Vector.ofFn fun h => buildPlane fun w => f (Fin.cons h w)

@[simp] theorem cubeMem_buildCube (f : Tuple 3 → Bool) (x : Tuple 3) :
    cubeMem (buildCube f) x = f x := by
  change planeMem ((Vector.ofFn _ : Cube).get (x 0)) (Fin.tail x) = _
  simp [Vector.get, Fin.cons_self_tail]

@[simp] theorem planeSet_or (p q : Plane) : planeSet (p ||| q) = planeSet p ∪ planeSet q := by
  ext x
  simp [planeMem]

@[simp] theorem planeSet_and (p q : Plane) : planeSet (p &&& q) = planeSet p ∩ planeSet q := by
  ext x
  simp [planeMem]

def cubeUnion (p q : Cube) : Cube := Vector.zipWith (· ||| ·) p q

def cubeInter (p q : Cube) : Cube := Vector.zipWith (· &&& ·) p q

@[simp] theorem cubeSet_union (p q : Cube) : cubeSet (cubeUnion p q) = cubeSet p ∪ cubeSet q := by
  ext x
  simp [cubeUnion, cubeMem, Vector.get]

@[simp] theorem cubeSet_inter (p q : Cube) : cubeSet (cubeInter p q) = cubeSet p ∩ cubeSet q := by
  ext x
  simp [cubeInter, cubeMem, Vector.get]

/-- Raw mask equality represents plane equality when the high bits are zero. -/
def Canonical (p : Plane) : Prop := ∀ i, 49 ≤ i → p.toNat.testBit i = false

@[simp] theorem canonical_buildPlane (f : Tuple 2 → Bool) : Canonical (buildPlane f) := by
  intro i hi
  simp [buildPlane, test_lowBits _ 49 _ (by decide), Nat.not_lt_of_ge hi]

theorem plane_eq_of_set_eq {p q : Plane} (hp : Canonical p) (hq : Canonical q)
    (heq : planeSet p = planeSet q) : p = q := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 49
  · have h := Finset.ext_iff.mp heq (pointAt i)
    simpa [planeMem, show index (pointAt i) = i from index_pointAt ⟨i, hi⟩] using h
  · rw [hp i (by omega), hq i (by omega)]

@[simp] theorem canonical_or {p q : Plane} (hp : Canonical p) (hq : Canonical q) :
    Canonical (p ||| q) := by
  intro i hi
  simp [hp i hi, hq i hi]

def lev (c : Cube) (k : Fin 3) (s : ZMod 7) : Plane :=
  buildPlane fun w => cubeMem c (k.insertNth (α := fun _ => ZMod 7) s w)

def cut (c : Cube) (k : Fin 3) (s : ZMod 7) : Plane := lev c k s ||| lev c k (s+1)

@[simp] theorem canonical_lev (c : Cube) (k : Fin 3) (s : ZMod 7) : Canonical (lev c k s) :=
  canonical_buildPlane _

@[simp] theorem canonical_cut (c : Cube) (k : Fin 3) (s : ZMod 7) : Canonical (cut c k s) :=
  canonical_or (canonical_lev c k s) (canonical_lev c k (s+1))

theorem planeSet_lev (c : Cube) (k : Fin 3) (s : ZMod 7) :
    planeSet (lev c k s) = ((cubeSet c).filter fun x => x k = s).image (k.removeNth ·) := by
  ext w
  simp only [mem_planeSet, lev, planeMem_buildPlane, Finset.mem_image, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨_, ⟨(mem_cubeSet ..).mpr h, Fin.insertNth_apply_same ..⟩, Fin.removeNth_insertNth ..⟩
  · rintro ⟨x, ⟨hx, rfl⟩, rfl⟩
    simpa only [Fin.insertNth_self_removeNth] using (mem_cubeSet c x).mp hx

theorem planeSet_cut (c : Cube) (k : Fin 3) (s : ZMod 7) :
    planeSet (cut c k s) = ((cubeSet c).filter fun x => x k = s ∨ x k = s+1).image
      (k.removeNth ·) := by
  rw [cut, planeSet_or, planeSet_lev, planeSet_lev, Finset.filter_or, Finset.image_union]

/-- Permute the input positions, optionally negate each residue, then translate. -/
abbrev Isometry (n : ℕ) := Equiv.Perm (Fin n) × (Fin n → Bool) × Tuple n

private def sign (b : Bool) (x : ZMod 7) := if b then -x else x

private theorem sign_twice (b : Bool) (x : ZMod 7) : sign b (sign b x) = x := by
  cases b <;> simp [sign]

def wordEquiv {n : ℕ} (g : Isometry n) : Tuple n ≃ Tuple n where
  toFun x k := sign (g.2.1 k) (x (g.1 k)) + g.2.2 k
  invFun y j := let k := g.1.symm j; sign (g.2.1 k) (y k - g.2.2 k)
  left_inv x := by ext j; simp [sign_twice]
  right_inv y := by ext k; simp [sign_twice]

def planeAct (g : Isometry 2) (p : Plane) : Plane :=
  buildPlane fun x => planeMem p ((wordEquiv g).symm x)

def cubeAct (g : Isometry 3) (c : Cube) : Cube :=
  buildCube fun x => cubeMem c ((wordEquiv g).symm x)

private theorem mem_image_equiv {α β : Type*} [DecidableEq β] (e : α ≃ β) (s : Finset α) (y : β) :
    e.symm y ∈ s ↔ y ∈ s.image e := by
  simp [Finset.mem_image, Equiv.apply_eq_iff_eq_symm_apply]

theorem planeSet_act (g : Isometry 2) (p : Plane) :
    planeSet (planeAct g p) = (planeSet p).image (wordEquiv g) := by
  ext x
  simpa only [mem_planeSet, planeAct, planeMem_buildPlane] using
    mem_image_equiv (wordEquiv g) (planeSet p) x

theorem cubeSet_act (g : Isometry 3) (c : Cube) :
    cubeSet (cubeAct g c) = (cubeSet c).image (wordEquiv g) := by
  ext x
  simpa only [mem_cubeSet, cubeAct, cubeMem_buildCube] using
    mem_image_equiv (wordEquiv g) (cubeSet c) x

/-- Advance one chosen coordinate by `t` modulo seven. -/
def shift (p : Plane) (k : Fin 2) (t : ZMod 7) : Plane :=
  planeAct (Equiv.refl _, fun _ => false, fun i => if i = k then t else 0) p

theorem planeSet_shift (p : Plane) (k : Fin 2) (t : ZMod 7) :
    planeSet (shift p k t) = (planeSet p).image (fun x i => x i + if i = k then t else 0) :=
  planeSet_act _ _

/-- Keep the bits that correspond to points. -/
@[inline] def clean (p : Plane) : Plane := p &&& 0x1ffffffffffff

@[simp] theorem planeMem_clean (p : Plane) (x : Tuple 2) : planeMem (clean p) x = planeMem p x := by
  simp only [planeMem, clean, UInt64.toNat_and, Nat.testBit_and]
  change (_ && (2^49-1 : Nat).testBit (index x)) = _
  rw [Nat.testBit_two_pow_sub_one]
  simp [index_lt]

theorem canonical_clean (p : Plane) : Canonical (clean p) := by
  intro i hi
  simp only [clean, UInt64.toNat_and, Nat.testBit_and]
  change (_ && (2^49-1 : Nat).testBit i) = false
  rw [Nat.testBit_two_pow_sub_one]
  simp [Nat.not_lt_of_ge hi]

/-- Each cyclic translation by one is the disjoint union of an ordinary shift
and a shift for the wrapped row or column. Masks specify the destination bits. -/
private structure Routing where
  left : UInt64
  leftMask : UInt64
  right : UInt64
  rightMask : UInt64

@[inline] private def routing (k : Fin 2) (plus : Bool) : Routing :=
  if k = 0 then
    if plus then ⟨7, 0x1ffffffffff80, 42, 0x7f⟩
    else ⟨42, 0x1fc0000000000, 7, 0x3ffffffffff⟩
  else
    if plus then ⟨1, 0x1fbf7efdfbf7e, 6, 0x40810204081⟩
    else ⟨6, 0x1020408102040, 1, 0xfdfbf7efdfbf⟩

/-- Cyclic translation by +1 or −1 on either plane axis, using two machine shifts. -/
@[inline] def step (p : Plane) (k : Fin 2) (plus : Bool) : Plane :=
  let r := routing k plus
  ((p <<< r.left) &&& r.leftMask) ||| ((p >>> r.right) &&& r.rightMask)

private def source (w : Tuple 2) (k : Fin 2) (t : Fin 3) : Tuple 2 :=
  fun j => if j = k then w j + ![(0 : ZMod 7), -1, 1] t else w j

/-- This finite check verifies only address arithmetic. The bits in `p` are
arbitrary in the theorem below. -/
private theorem routing_correct : ∀ (k : Fin 2) (plus : Bool) (w : Tuple 2),
    let r := routing k plus
    let i := index w
    let j := index (source w k (if plus then 1 else 2))
    (r.leftMask.toNat.testBit i = true ∧ r.rightMask.toNat.testBit i = false ∧
      r.left.toNat % 64 ≤ i ∧ i - r.left.toNat % 64 = j) ∨
    (r.leftMask.toNat.testBit i = false ∧ r.rightMask.toNat.testBit i = true ∧
      r.right.toNat % 64 + i = j) := by decide

private theorem planeMem_step (p : Plane) (k : Fin 2) (plus : Bool) (w : Tuple 2) :
    planeMem (step p k plus) w = planeMem p (source w k (if plus then 1 else 2)) := by
  have h64 : index w < 64 := Nat.lt_trans (index_lt w) (by decide)
  have h := routing_correct k plus w
  dsimp only at h
  simp only [planeMem, step, UInt64.toNat_or, Nat.testBit_or, UInt64.toNat_and, Nat.testBit_and,
    UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  rcases h with ⟨hl, hr, hn, heq⟩ | ⟨hl, hr, heq⟩ <;> simp [*]

theorem planeMem_step_plus (p : Plane) (k : Fin 2) (w : Tuple 2) :
    planeMem (step p k true) w = planeMem p (fun j => if j = k then w j - 1 else w j) := by
  rw [planeMem_step]
  congr 1
  ext j
  simp [source, sub_eq_add_neg]

theorem planeMem_step_minus (p : Plane) (k : Fin 2) (w : Tuple 2) :
    planeMem (step p k false) w = planeMem p (fun j => if j = k then w j + 1 else w j) := by
  rw [planeMem_step]
  rfl

/-- Add the two cyclic neighbours on a single axis. -/
@[inline] private def spread (p : Plane) (k : Fin 2) := p ||| step p k true ||| step p k false

private theorem planeMem_spread (p : Plane) (k : Fin 2) (w : Tuple 2) :
    planeMem (spread p k) w ↔ ∃ t : Fin 3, planeMem p (source w k t) := by
  have hz : source w k 0 = w := by ext j; simp [source]
  have h (p q : Plane) : planeMem (p ||| q) w = (planeMem p w || planeMem q w) := by
    simp [planeMem]
  simp only [spread, h, planeMem_step, ↓reduceIte, Bool.or_eq_true, Fin.exists_fin_succ,
    Fin.isValue, Fin.succ_zero_eq_one, hz, Fin.exists_fin_zero, or_false]
  tauto

/-- Closed neighbourhood for the strong product, computed by spreading once
along each coordinate of the square torus. -/
@[inline] def neighbourhood (p : Plane) : Plane := clean (spread (spread p 0) 1)

private theorem coordinate_neighbours : ∀ x y : Tuple 2,
    (∃ a b : Fin 3, source (source x 1 b) 0 a = y) ↔ ∀ i, cycleStep (x i) (y i) := by
  unfold cycleStep
  decide +kernel

theorem mem_neighbourhood (p : Plane) (x : Tuple 2) : x ∈ planeSet (neighbourhood p) ↔
    ∃ y ∈ planeSet p, ∀ i, cycleStep (x i) (y i) := by
  simp only [mem_planeSet, neighbourhood, planeMem_clean, planeMem_spread]
  constructor
  · rintro ⟨b, a, h⟩
    exact ⟨_, h, (coordinate_neighbours ..).mp ⟨a, b, rfl⟩⟩
  · rintro ⟨y, hy, hc⟩
    obtain ⟨a, b, rfl⟩ := (coordinate_neighbours ..).mpr hc
    exact ⟨b, a, hy⟩

end SevenCycle.Bitsets
