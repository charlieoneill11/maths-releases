import SevenCycleRuntime.TypeThree
import SevenCycleRuntime.Adjacent

namespace SevenCycle.Adjacent.BandJoin

abbrev PackedCube := Vector UInt64 7

/-- A transverse axis numbered from zero, its physical start, its gap, and the
number of words already fixed at its centre in the anchor slab. -/
structure Port where
  axis : Fin 3
  start : Fin 7
  gap : Nat
  known : Nat
deriving Inhabited

abbrev Ports := Vector Port 6
abbrev Domains := Vector (Array PackedCube) 6

def axisOf (i : Fin 6) : Fin 3 := ⟨i.val / 2, by have := i.isLt; omega⟩

def later (i : Fin 6) : Bool := i.val % 2 == 1

/-- Place the two starts on each of the three transverse axes. -/
def portsFor (bases : Vector (Fin 7) 3) (gaps known : Vector Nat 3) : Ports :=
  Vector.ofFn fun i =>
    let a := axisOf i
    let t := bases.get a
    ⟨a, if later i then t + Fin.ofNat 7 (gaps.get a) else t, gaps.get a, known.get a⟩

/-- Number of the queried transverse coordinate after deleting another
transverse coordinate. The anchor coordinate remains first. -/
def transverse (a b : Fin 3) : Fin 3 := Fin.ofNat 3 (if b < a then b.val+1 else b.val)

def exteriorCommon (r w : PackedCube) : Nat :=
  let n := SevenCycleRuntime.Adjacent.maskCard
  n (r.get 3 &&& w.get 3) + n (r.get 4 &&& w.get 4) +
  n (r.get 5 &&& w.get 5) + n (r.get 6 &&& w.get 6)

def pairOK (s t : Port) (r w : PackedCube) : Bool :=
  if s.axis = t.axis then
    s.gap != 1 || 16 ≤ s.known + exteriorCommon r w
  else
    SevenCycle.TypeThree.fastCut r (transverse s.axis t.axis) t.start ==
      SevenCycle.TypeThree.fastCut w (transverse t.axis s.axis) s.start

/-- A failed pair test discards the placement before the full six-way DFS. -/
def pairsPossible (ports : Ports) (domains : Domains) : Bool :=
  (Array.finRange 6).all fun i => (Array.finRange 6).all fun j =>
    i.val ≥ j.val || (domains.get i).any fun r =>
      (domains.get j).any fun w => pairOK (ports.get i) (ports.get j) r w

private def scan (ports : Ports) (domains : Domains)
    (chosen : Array (Fin 6 × PackedCube)) : Nat → Bool
  | 0 => true
  | n+1 =>
    if h : n < 6 then
      let i : Fin 6 := ⟨n,h⟩
      (domains.get i).any fun r =>
        chosen.all (fun (j,w) => pairOK (ports.get i) (ports.get j) r w) &&
          scan ports domains (chosen.push (i,r)) n
    else false

def canJoin (ports : Ports) (domains : Domains) : Bool :=
  pairsPossible ports domains && scan ports domains #[] 6

/-- A selection of one cube at each port survives the executable join when
all its physical pair checks succeed. -/
theorem canJoin_of_selection (ports : Ports) (domains : Domains) (w : Fin 6 → PackedCube)
    (mem : ∀ i, w i ∈ domains.get i)
    (pairs : ∀ i j, i ≠ j → pairOK (ports.get i) (ports.get j) (w i) (w j) = true) :
    canJoin ports domains = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i _
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro j _
    by_cases h : i.val ≥ j.val
    · simp [h]
    · apply Bool.or_eq_true_iff.mpr
      exact Or.inr (Array.any_eq_true'.mpr ⟨_,mem i,Array.any_eq_true'.mpr
        ⟨_,mem j,pairs i j (fun e => h (e ▸ Nat.le_refl _))⟩⟩)
  · have go (n : Nat) (hn : n ≤ 6) (a : Array (Fin 6 × PackedCube))
        (ha : ∀ e ∈ a, n ≤ e.1.val ∧ e.2 = w e.1) : scan ports domains a n = true := by
      induction n generalizing a with
      | zero => rfl
      | succ n ih =>
        let i : Fin 6 := ⟨n,hn⟩
        rw [scan, dif_pos (show n < 6 from hn)]
        apply Array.any_eq_true'.mpr
        refine ⟨w i, mem i, Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
        · apply Array.all_eq_true_iff_forall_mem.mpr
          rintro ⟨j,v⟩ hv
          obtain ⟨lt, same⟩ := ha _ hv
          change v = w j at same
          change pairOK (ports.get i) (ports.get j) (w i) v = true
          rw [same]
          exact pairs i j fun e => (Nat.ne_of_lt lt) (congrArg Fin.val e)
        · apply ih (Nat.le_of_succ_le hn)
          intro e he
          rcases Array.mem_push.mp he with he | rfl
          · exact ⟨Nat.le_of_succ_le (ha _ he).1,(ha _ he).2⟩
          · exact ⟨Nat.le_refl _,rfl⟩
    exact go 6 (Nat.le_refl _) #[] (by simp)

end SevenCycle.Adjacent.BandJoin
