import SevenCycle.Proof.Model
import SevenCycle.AtlasData
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod

/-! # Mathematical definitions shared by the proof teams -/

namespace SevenCycle.Blueprint

local notation "Word" => Proof.Tuple
local notation "IsCode" => Proof.packing Proof.cycleStep
local notation "Confusable" => Proof.conflict Proof.cycleStep

/-- Permutation of the input coordinates, sign bits and output translations. -/
abbrev Isometry (n : ℕ) := Equiv.Perm (Fin n) × (Fin n → Bool) × Word n

def act {n : ℕ} (g : Isometry n) (x : Word n) : Word n := fun k =>
  (if g.2.1 k then -x (g.1 k) else x (g.1 k)) + g.2.2 k

def dropCoord {n : ℕ} (k : Fin (n+1)) (x : Word (n+1)) : Word n :=
  fun j => x (k.succAbove j)

def level {n : ℕ} (C : Finset (Word (n+1))) (k : Fin (n+1)) (i : ZMod 7) :=
  C.filter fun x => x k = i

def band {n : ℕ} (C : Finset (Word (n+1))) (k : Fin (n+1)) (i : ZMod 7) :=
  C.filter fun x => x k = i ∨ x k = i + 1

def deficit (C : Finset (Word 4)) (k : Fin 4) (i : ZMod 7) : ℕ := 33 - (band C k i).card

def fullStarts (C : Finset (Word 4)) (k : Fin 4) : Finset (ZMod 7) :=
  Finset.univ.filter fun i => (band C k i).card = 33

def HasCentre (C : Finset (Word 4)) (k : Fin 4) (c : ZMod 7) : Prop :=
  c - 1 ∈ fullStarts C k ∧ c ∈ fullStarts C k ∧
    16 ≤ (level C k c).card ∧ (level C k c).card ≤ 19

def cycleDistance (i j : ZMod 7) : ℕ := min (i-j).val (j-i).val

def AxisGap (C : Finset (Word 4)) (k : Fin 4) (d : ℕ) : Prop :=
  (∃ i ∈ fullStarts C k, ∃ j ∈ fullStarts C k, i ≠ j ∧ cycleDistance i j = d) ∧
    ∀ i ∈ fullStarts C k, ∀ j ∈ fullStarts C k, i ≠ j → d ≤ cycleDistance i j

/-- A profile records four least distances, retaining multiplicities and forgetting axis order. -/
def HasProfile (C : Finset (Word 4)) (p : Multiset ℕ) : Prop :=
  ∃ d : Fin 4 → Fin 3, (∀ k, AxisGap C k ((d k).val + 1)) ∧
    p = (Finset.univ : Finset (Fin 4)).val.map (fun k => (d k).val + 1)

/-! ### The atlas in dimensions two and three -/

/-- Transport every word by the same signed affine coordinate permutation. -/
def actOnCode {n : ℕ} (g : Isometry n) (C : Finset (Word n)) : Finset (Word n) :=
  C.image (act g)

def twoRepresentatives : Fin 3 → Finset (Word 2) :=
  ![{![0, 0], ![0, 2], ![1, 4], ![2, 0], ![2, 2], ![3, 4], ![4, 1], ![4, 6], ![5, 3], ![6, 5]},
    {![0, 0], ![0, 2], ![1, 4], ![2, 0], ![3, 2], ![3, 4], ![4, 6], ![5, 1], ![5, 3], ![6, 5]},
    {![0, 0], ![0, 2], ![1, 4], ![2, 1], ![2, 6], ![3, 3], ![4, 0], ![4, 5], ![5, 2], ![6, 4]}]

/-- Mathematical interpretation of the released plane masks, with bit 7*y+z at height x. -/
def atlasRepresentative (r : Fin atlasPlanes.size) : Finset (Word 3) :=
  Finset.univ.filter fun x =>
    (atlasPlanes[r].get (x 0)).toNat.testBit (7 * (x 1).val + (x 2).val)

noncomputable def stabilizerOrder (r : Fin atlasPlanes.size) : ℕ :=
  (Finset.univ.filter (fun g : Isometry 3 => actOnCode g (atlasRepresentative r) =
    atlasRepresentative r)).card

/-! ### Projections, slabs and matchings -/

def projectedBand {n : ℕ} (C : Finset (Word (n+1))) (k : Fin (n+1)) (i : ZMod 7) :
    Finset (Word n) := (band C k i).image (dropCoord k)

def projectedLevel {n : ℕ} (C : Finset (Word (n+1))) (k : Fin (n+1)) (i : ZMod 7) :
    Finset (Word n) := (level C k i).image (dropCoord k)

abbrev cut (W : Finset (Word 3)) (m : Fin 3) (s : ZMod 7) := projectedBand W m s
abbrev lev (W : Finset (Word 3)) (m : Fin 3) (s : ZMod 7) := projectedLevel W m s

def adjacentSignature (W : Finset (Word 3)) (m : Fin 3) (s : ZMod 7) :=
  (cut W m s, cut W m (s+1), lev W m (s+1))

/-- Edges of the conflict graph include identical words on the two different sides. -/
def conflictEdge (x y : Word 3) : Prop := x = y ∨ Confusable x y

namespace SearchSpec

/- Mathematical stage outputs for §§5–7. All axes retain their ambient labels.
Deleting an axis replaces its coordinate by zero, so projections from two
directions can be compared after the second deletion. These predicates specify
sets of candidates. The executable stage outputs must still be related to them.
They range over all labelled faces. Atlas normalisation and symmetry reduction
are obligations of an implementation using representatives. -/

/-- What it means for stored rows, possibly chunked or reduced by symmetry,
to retain a mathematical configuration. The decoding relation can include
the axis frame, the chunk index, and the isometry used in normalisation. -/
def Retained {Row Config : Type*} (rows : Array Row)
    (represents : Row → Config → Prop) (c : Config) : Prop :=
  ∃ r ∈ rows, represents r c

/-- A stage implementation must prove coverage for the predicate used by
its retention lemma. An incomplete or empty array cannot supply this proof
merely from facts about the rows it actually contains. -/
def Covers {Row Config : Type*} (wins : Config → Prop)
    (rows : Array Row) (represents : Row → Config → Prop) : Prop :=
  ∀ c, wins c → Retained rows represents c

abbrev Points := Finset (Word 4)
abbrev Axis := Fin 4
abbrev Height := ZMod 7

structure Frame where
  gap : Axis → ℕ
  base : Axis → Height

def start (m : Frame) (k : Axis) (b : Bool) : Height :=
  if b then m.base k + (m.gap k : Height) else m.base k

def ValidFrame (m : Frame) : Prop := ∀ k, 1 ≤ m.gap k ∧ m.gap k ≤ 3

def Marked (m : Frame) (C : Points) : Prop :=
  ValidFrame m ∧ (∀ k b, start m k b ∈ fullStarts C k) ∧
  ∀ k, m.gap k = 1 → HasCentre C k (start m k true)

def setHeight (x : Word 4) (k : Axis) (h : Height) : Word 4 :=
  Function.update x k h

def face (D : Points) (k : Axis) (p : Height → Prop) [DecidablePred p] : Points :=
  (D.filter fun x => p (x k)).image fun x => setHeight x k 0

def plane (D : Points) (k : Axis) (t : Height) : Points :=
  face D k (fun z => z = t)

def stripe (D : Points) (k : Axis) (t : Height) : Points :=
  face D k (fun z => z = t ∨ z = t+1)

def Face33 (k : Axis) (W : Points) : Prop :=
  W.card = 33 ∧ IsCode W ∧ ∀ x ∈ W, x k = 0

abbrev Family := Axis → Bool → Points

def projections (m : Frame) (C : Points) : Family :=
  fun k b => stripe C k (start m k b)

/-- Crossings for marked bands on pairs of distinct axes in a given set. -/
def Crossings (m : Frame) (axes : Axis → Prop) (W : Family) : Prop :=
  ∀ k l, axes k → axes l → k ≠ l → ∀ b c,
    stripe (W k b) l (start m l c) = stripe (W l c) k (start m k b)

def FitsCuts (m : Frame) (k l : Axis) (s : Height) (S T W : Points) : Prop :=
  stripe S l s = stripe W k (start m k false) ∧
  stripe T l s = stripe W k (start m k true)

/-- Used in the planar filters of all three searches. Each transverse band
may choose its own witness, before the joint choice tested by the joins. -/
def Contacts (m : Frame) (k : Axis) (S T : Points) : Prop :=
  ∀ l, l ≠ k → ∀ b, ∃ W, Face33 l W ∧ FitsCuts m k l (start m l b) S T W

def joined (m : Frame) (k : Axis) (S T : Points) (W : Family) : Prop :=
  (∀ l, l ≠ k → ∀ b, Face33 l (W l b) ∧
    FitsCuts m k l (start m l b) S T (W l b)) ∧
  Crossings m (fun l => l ≠ k) W

/-- Adjacent Stage 1, before reducing the first support to an atlas class. -/
def AdjSupport (k : Axis) (S T : Points) : Prop :=
  Face33 k S ∧ Face33 k T ∧ 16 ≤ (S ∩ T).card

def AdjMiddle (m : Frame) (k : Axis) (S T U : Points) : Prop :=
  U ⊆ S ∩ T ∧ 16 ≤ U.card ∧ U.card ≤ 19 ∧
  ∀ l, l ≠ k → ∀ b, ∃ W, Face33 l W ∧ FitsCuts m k l (start m l b) S T W ∧
    stripe U l (start m l b) = plane W k (start m k true)

def liftTo (D : Points) (k : Axis) (h : Height) : Points :=
  D.image fun x => setHeight x k h

def slab (m : Frame) (k : Axis) (S T U : Points) : Points :=
  liftTo (S \ U) k (m.base k) ∪ liftTo U k (start m k true) ∪
    liftTo (T \ U) k (start m k true + 1)

def inSlab (m : Frame) (k : Axis) (x : Word 4) : Prop :=
  x k ∈ ({m.base k, start m k true, start m k true + 1} : Finset Height)

instance (m : Frame) (k : Axis) (x : Word 4) : Decidable (inSlab m k x) := by
  unfold inSlab
  infer_instance

def CentreCapacity (m : Frame) (k l : Axis) (D : Points) (W : Family) : Prop :=
  16 ≤ (D.filter fun x => x l = start m l true).card +
    ((W l false ∩ W l true).filter fun x => ¬ inSlab m k x).card

def AdjSixBand (m : Frame) (k : Axis) (S T U : Points) (W : Family) : Prop :=
  joined m k S T W ∧
  (∀ l, l ≠ k → ∀ b,
    stripe U l (start m l b) = plane (W l b) k (start m k true)) ∧
  ∀ l, l ≠ k → m.gap l = 1 → CentreCapacity m k l (slab m k S T U) W

def RecordedSlab (m : Frame) (k : Axis) (D : Points) : Prop :=
  ∃ S T U W, AdjSupport k S T ∧ Contacts m k S T ∧ AdjMiddle m k S T U ∧
    AdjSixBand m k S T U W ∧ D = slab m k S T U

def inUnion (m : Frame) (x : Word 4) : Prop :=
  ∃ k, m.gap k = 1 ∧ inSlab m k x

instance (m : Frame) (x : Word 4) : Decidable (inUnion m x) := by
  unfold inUnion
  infer_instance

def AdjUnion (m : Frame) (D : Points) : Prop :=
  ∃ V : Axis → Points,
    (∀ k, m.gap k = 1 → RecordedSlab m k (V k)) ∧
    (∀ k l, m.gap k = 1 → m.gap l = 1 →
      (V k).filter (inSlab m l) = (V l).filter (inSlab m k)) ∧
    (∀ x, x ∈ D ↔ ∃ k, m.gap k = 1 ∧ x ∈ V k) ∧ IsCode D

/-- The exterior for profile 1111. -/
def Exterior (m : Frame) (D E : Points) : Prop :=
  (∀ x ∈ E, ¬ inUnion m x) ∧ IsCode (D ∪ E)

/-- The Stage 6 test on the remaining marked bands of a mixed profile. -/
def Remaining (m : Frame) (D : Points) (W : Family) : Prop :=
  Crossings m (fun k => m.gap k ≠ 1) W ∧
  ∀ k, m.gap k ≠ 1 → ∀ b,
    let t := start m k b
    Face33 k (W k b) ∧ ((W k b).filter (inUnion m)) = stripe D k t ∧
    ∀ y ∈ W k b, ¬ inUnion m y →
      ∃ h, (h = t ∨ h = t + 1) ∧ setHeight y k h ∉ D ∧
        ∀ x ∈ D, ¬ Confusable (setHeight y k h) x

/-- An arbitrary perfect matching, represented by its graph on the two faces. -/
def Perfect (S T : Points) (M : Finset (Word 4 × Word 4)) : Prop :=
  (∀ e ∈ M, e.1 ∈ S ∧ e.2 ∈ T ∧ (e.1 = e.2 ∨ Confusable e.1 e.2)) ∧
  (∀ x ∈ S, ∃! y, (x, y) ∈ M) ∧ (∀ y ∈ T, ∃! x, (x, y) ∈ M)

def TwoMiddle (m : Frame) (k : Axis) (S T X Y : Points)
    (M : Finset (Word 4 × Word 4)) : Prop :=
  X ⊆ S ∧ Y ⊆ T ∧ 14 ≤ X.card ∧ X.card ≤ 19 ∧ 14 ≤ Y.card ∧ Y.card ≤ 19 ∧
  (∀ e ∈ M, ¬ (e.1 ∈ X ∧ e.2 ∈ Y)) ∧
  (M.filter fun e => e.1 ∉ X ∧ e.2 ∉ Y).card ≤ 2 ∧
  ∀ l, l ≠ k → ∀ b, ∃ W, Face33 l W ∧ FitsCuts m k l (start m l b) S T W ∧
    stripe X l (start m l b) = plane W k (m.base k + 1) ∧
    stripe Y l (start m l b) = plane W k (start m k true)

def TwoProjections (m : Frame) (k : Axis) (S T X Y : Points) (W : Family) : Prop :=
  joined m k S T W ∧ Disjoint X Y ∧ IsCode (X ∪ Y) ∧
  ∀ l, l ≠ k → ∀ b,
    stripe X l (start m l b) = plane (W l b) k (m.base k + 1) ∧
    stripe Y l (start m l b) = plane (W l b) k (start m k true)

/-- For a true type-two frame no axis has consecutive full bands. This
condition supplies the 31-word middle-band bound in Lemma 4(3). -/
def NoConsecutive (C : Points) : Prop :=
  ∀ k t, t ∈ fullStarts C k → t + 1 ∉ fullStarts C k

end SearchSpec

end SevenCycle.Blueprint
