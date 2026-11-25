import SevenCycle.TypeTwo.Ports

/-! ## Joining six transverse projections

The DFS checks all past projections when adding a new one. Every crossing,
overlap prescription, and conflict between a left and a right endpoint involves
at most two projections, so all tests can be applied at insertion time.
-/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry

structure Slot where
  axis : Axis
  height : Height

abbrev Slots := Vector Slot 6
abbrev Domains := Vector (Array Bitsets.Cube) 6

/-- Read the four cyclic differences through equality tests on their residues. -/
def close4 (x y : Tuple 4) : Bool :=
  (Array.finRange 4).all fun k =>
    let d := x k - y k
    d == -1 || (d == 0 || d == 1)

private theorem close4_eq (x y : Tuple 4) :
    close4 x y = decide (∀ k : Fin 4, x k - y k ∈ ({-1,0,1} : Finset Height)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [close4, Array.all_eq_true_iff_forall_mem, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h k
    exact h k (Array.mem_ofFn.mpr ⟨k,rfl⟩)
  · exact fun h k _ => h k

/-- A conflict matrix in matching-edge order. Row i contains the right
endpoints that coincide with or are confusable with left endpoint i. -/
def conflictMatrix (f : ℕ → Edge) : Vector Mask 33 :=
  Vector.ofFn fun i => pack (fun j => close4 (f i).1 (f j).2) 33

def independent (mat : Vector Mask 33) (x y : Mask) : Bool :=
  (Array.finRange 33).all fun i => !x.getLsbD i || (mat[i.val] &&& y == 0)

private theorem conflict_bit (f : ℕ → Edge) (i : Fin 33) (j : ℕ) (hj : j < 33) :
    (conflictMatrix f)[i.val].getLsbD j =
      decide (∀ h : Fin 4, (f i).1 h - (f j).2 h ∈ ({-1, 0, 1} : Finset Height)) := by
  simp only [conflictMatrix, Vector.getElem_ofFn, pack_bit _ _ _ hj, close4_eq]

private theorem independent_true {X Y : Points}
    (f : ℕ → Edge) (hd : Disjoint X Y) (hc : packing cycleStep (X ∪ Y)) (a : Mark)
    (ha : Realizes (leftOf f X) (rightOf f Y) a) :
    independent (conflictMatrix f) a.leftIn a.rightIn := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro i _
  by_cases hleft : a.leftIn.getLsbD i
  · have hx : (f i).1 ∈ X := by
      have hh := hleft
      rw [ha.1, BitVec.getLsbD_and] at hh
      simpa only [leftOf, pack_bit _ _ _ i.isLt, decide_eq_true_eq] using (Bool.and_eq_true_iff.mp hh).2
    have eqzero : (conflictMatrix f)[i.val] &&& a.rightIn = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      by_cases hright : a.rightIn.getLsbD j
      · have hy : (f j).2 ∈ Y := by
          have hh := hright
          rw [ha.2, BitVec.getLsbD_and] at hh
          simpa only [rightOf, pack_bit _ _ _ hj, decide_eq_true_eq] using (Bool.and_eq_true_iff.mp hh).2
        have hn : (f i).1 ≠ (f j).2 := fun e =>
          Finset.disjoint_left.mp hd (e ▸ hx) hy
        have nclose : ¬ ∀ h, (f i).1 h - (f j).2 h ∈
            ({-1, 0, 1} : Finset Height) := fun h =>
          hc _ (Finset.mem_union_left _ hx) _ (Finset.mem_union_right _ hy) ⟨hn,h⟩
        rw [BitVec.getLsbD_and, conflict_bit _ _ _ hj, decide_eq_false nclose, Bool.false_and]
        exact (BitVec.getLsbD_zero ..).symm
      · rw [BitVec.getLsbD_and, Bool.eq_false_of_not_eq_true hright, Bool.and_false]
        exact (BitVec.getLsbD_zero ..).symm
    simp [eqzero]
  · rw [Bool.eq_false_of_not_eq_true hleft]
    rfl

/-- Both crossing keys are computed on exactly the same ambient coordinate
samples. The order of the two erased axes is fixed before sampling. -/
def sample (a b : Axis) (z : Tuple 2) : Tuple 4 :=
  if a < b then
    let rest := (0 : Fin 3).predAbove b
    a.insertNth (α := fun _ => Height) 0 (rest.insertNth (α := fun _ => Height) 0 z)
  else
    let rest := (0 : Fin 3).predAbove a
    b.insertNth (α := fun _ => Height) 0 (rest.insertNth (α := fun _ => Height) 0 z)

private theorem sample_swap {a b : Axis} (hne : a ≠ b) (z : Tuple 2) :
    sample a b z = sample b a z := by
  rcases lt_or_gt_of_ne hne with h|h <;> simp [sample, h, not_lt_of_gt h]

def cutReader (r : Bitsets.Cube) (l k : Axis) (h : Height) (x : Tuple 4) : Bool :=
  planeReader r l k h x || planeReader r l k (h+1) x

private theorem cutReader_spec {r : Bitsets.Cube} {W : Points} {l k : Axis} (hne : k ≠ l)
    (hflat : ∀ x ∈ W, x l = 0) (hr : Stores r l W) (h : Height) (u : Tuple 4) :
    cutReader r l k h u ↔ u ∈ stripe W k h := by
  rw [← FrameGeometry.plane_union]
  simp only [cutReader, Bool.or_eq_true, planeReader_spec hne hflat hr, Finset.mem_union]

structure Candidate where
  slot : Fin 6
  mark : Mark
  keys : Vector Bitsets.Plane 6

def candidate (f : ℕ → Edge) (s : Slots) (k : Axis) (inner outer : Height)
    (j : Fin 6) (r : Bitsets.Cube) : Candidate :=
  let l := s[j].axis
  let t := s[j].height
  { slot := j
    mark := markFromPlanes f l t (planeReader r l k inner) (planeReader r l k outer)
    keys := Vector.ofFn fun i => Bitsets.buildPlane fun z =>
      cutReader r l s[i].axis s[i].height (sample l s[i].axis z) }

/-- Check a pair, including both orientations of the conflict matrix via the union.
The same-axis comparison only uses the middle-level prescriptions. -/
def compatible (s : Slots) (mat : Vector Mask 33) (a b : Candidate) : Bool :=
  (s[a.slot].axis == s[b.slot].axis || a.keys[b.slot] == b.keys[a.slot]) &&
    agrees a.mark b.mark &&
    independent mat (a.mark.leftIn ||| b.mark.leftIn) (a.mark.rightIn ||| b.mark.rightIn)

def joinSearch (s : Slots) (mat : Vector Mask 33) (domains : Array (Array Candidate)) :
    ℕ → Array Candidate → Bool
  | 0, _ => true
  | n+1, chosen => (domains[n]?.getD #[]).any fun b =>
      independent mat b.mark.leftIn b.mark.rightIn &&
      chosen.all (compatible s mat b) &&
      joinSearch s mat domains n (chosen.push b)

def rejectsJoin (s : Slots) (f : ℕ → Edge) (k : Axis) (inner outer : Height) (domains : Domains) : Bool :=
  let rows := Array.ofFn fun j : Fin 6 => domains[j].map (candidate f s k inner outer j)
  !(joinSearch s (conflictMatrix f) rows 6 #[])

private theorem joinSearch_retains (s : Slots) (mat : Vector Mask 33)
    (domains : Array (Array Candidate)) (good : Candidate → Prop)
    (hself : ∀ a, good a → independent mat a.mark.leftIn a.mark.rightIn)
    (hpair : ∀ a b, good a → good b → compatible s mat a b)
    (hdom : ∀ j : Fin domains.size, ∃ a ∈ domains[j], good a)
    (n : ℕ) (hn : n ≤ domains.size) (chosen : Array Candidate) (hchosen : ∀ a ∈ chosen, good a) :
    joinSearch s mat domains n chosen := by
  induction n generalizing chosen with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b, hb, hg⟩ := hdom ⟨n,hn⟩
    rw [joinSearch, Array.getElem?_eq_getElem (show n < domains.size from hn)]
    apply Array.any_eq_true'.mpr
    refine ⟨b, hb, ?_⟩
    simp only [Bool.and_eq_true]
    refine ⟨⟨hself b hg, Array.all_eq_true_iff_forall_mem.mpr fun a ha => hpair b a hg (hchosen a ha)⟩, ?_⟩
    apply ih (by omega)
    intro a ha
    rcases Array.mem_push.mp ha with ha | rfl
    · exact hchosen a ha
    · exact hg

private theorem crossing_key {C : Points} {l q : Axis} (hne : l ≠ q) (t u : Height)
    {r w : Bitsets.Cube} (hr : Stores r l (stripe C l t)) (hw : Stores w q (stripe C q u)) :
    Bitsets.buildPlane (fun z => cutReader r l q u (sample l q z)) =
      Bitsets.buildPlane (fun z => cutReader w q l t (sample q l z)) := by
  have flat (i : Axis) (v : Height) (x : Tuple 4) (hx : x ∈ stripe C i v) : x i = 0 := by
    obtain ⟨_,_,_,rfl⟩ := mem_face.mp hx
    simp [setHeight]
  congr 1
  funext z
  apply Bool.eq_iff_iff.mpr
  rw [sample_swap hne, cutReader_spec hne.symm (flat l t) hr,
    cutReader_spec hne (flat q u) hw, stripe_comm C hne t u]

/-- A join domain retains the actual cube at each of the six indexed ports. -/
def CoversJoin (C : Points) (k : Axis) (s : Slots) (d : Domains) : Prop :=
  ∀ j : Fin 6, s[j].axis ≠ k ∧ ∃ r ∈ d[j], Stores r s[j].axis (stripe C s[j].axis s[j].height)

/-- Rejection of the six-domain join excludes every code that induces the
anchor faces and has its six transverse projections in the supplied domains. -/
theorem rejectsJoin_excludes_code_of_endpoints
    {C : Points} {m : Frame} {k : Axis}
    (hm : Marked m C) (hk : m.gap k = 2)
    (f : ℕ → Edge)
    (hf : ∀ i < 33, (f i).1 ∈ projections m C k false ∧ (f i).2 ∈ projections m C k true)
    (s : Slots) (d : Domains) (hd : CoversJoin C k s d)
    (hcheck : rejectsJoin s f k (m.base k+1) (start m k true) d = true) :
    ¬ packing cycleStep C := by
  intro hC
  let inner := m.base k+1
  let outer := start m k true
  let cand := candidate f s k inner outer
  let rows := Array.ofFn fun j : Fin 6 => d[j].map (cand j)
  let good (a : Candidate) := ∃ (j : Fin 6) (r : Bitsets.Cube), a = cand j r ∧
    Stores r s[j].axis (stripe C s[j].axis s[j].height)
  have hs := stripe_packing hC k (start m k false)
  have ht := stripe_packing hC k (start m k true)
  obtain ⟨_, hdisj, hpack, _⟩ := projections_retain hC hm hk
  let x := leftOf f (plane C k inner)
  let y := rightOf f (plane C k outer)
  have real (a : Candidate) (ha : good a) : Realizes x y a.mark := by
    obtain ⟨j, r, rfl, hrep⟩ := ha
    have hne := (hd j).1
    have flat : ∀ u ∈ stripe C s[j].axis s[j].height, u s[j].axis = 0 := by
      intro u hu
      obtain ⟨_,_,_,rfl⟩ := mem_face.mp hu
      simp [setHeight]
    have eq (h : Height) (u : Tuple 4) : planeReader r s[j].axis k h u ↔
        u ∈ stripe (plane C k h) s[j].axis s[j].height := by
      rw [planeReader_spec hne.symm flat hrep,
        show stripe (plane C k h) s[j].axis s[j].height =
          plane (stripe C s[j].axis s[j].height) k h from
          face_comm C hne.symm (fun z => z = h) (fun z => z = s[j].height ∨ z = s[j].height+1)]
    apply markFromPlanes_of_endpoints f hf hs ht _ _ _ _ _ _ (eq inner) (eq outer)
    · exact Adjacent.plane_sub_stripe (Or.inr rfl)
    · exact Adjacent.plane_sub_stripe (Or.inl rfl)
  have hpairs (a b : Candidate) (ha : good a) (hb : good b) : compatible s (conflictMatrix f) a b := by
    have hra := real a ha
    have hrb := real b hb
    have ind := independent_true f hdisj hpack (combine a.mark b.mark) (combine_realizes hra hrb)
    simp only [compatible, Bool.and_eq_true]
    refine ⟨⟨?_, agrees_of_realizes hra hrb⟩, ind⟩
    obtain ⟨j,r,rfl,hr⟩ := ha
    obtain ⟨j',w,rfl,hw⟩ := hb
    by_cases e : s[j].axis = s[j'].axis
    · exact Bool.or_eq_true_iff.mpr (.inl (beq_iff_eq.mpr e))
    · apply Bool.or_eq_true_iff.mpr
      apply Or.inr
      apply beq_iff_eq.mpr
      change ((Vector.ofFn _ : Vector Bitsets.Plane 6)[j'.val]) =
        ((Vector.ofFn _ : Vector Bitsets.Plane 6)[j.val])
      simp only [Vector.getElem_ofFn]
      exact crossing_key e _ _ hr hw
  have cover : ∀ j : Fin rows.size, ∃ a ∈ rows[j], good a := by
    intro i
    have hi : i.val < 6 := by simpa [rows] using i.isLt
    let j : Fin 6 := ⟨i.val,hi⟩
    obtain ⟨r,hr,hstore⟩ := (hd j).2
    have here : rows[i] = d[j].map (cand j) := Array.getElem_ofFn (i := i.val) ..
    exact ⟨cand j r, here ▸ Array.mem_map_of_mem hr, j, r, rfl, hstore⟩
  have run := joinSearch_retains s (conflictMatrix f) rows good
    (fun a ha => independent_true f hdisj hpack _ (real a ha)) hpairs cover 6
    (by simp [rows]) #[] (by simp)
  change (!(joinSearch s (conflictMatrix f) rows 6 #[])) = true at hcheck
  simp [run] at hcheck

/-- Rejection of the six-domain join excludes every code that induces the
anchor faces and has its six transverse projections in the supplied domains. -/
theorem rejectsJoin_excludes_code
    {C : Points} {m : Frame} {k : Axis} {M : Finset Edge}
    (hm : Marked m C) (hk : m.gap k = 2)
    (hM : Perfect (projections m C k false) (projections m C k true) M) (n : Numbering M)
    (s : Slots) (d : Domains) (hd : CoversJoin C k s d)
    (hcheck : rejectsJoin s n.edgeAt k (m.base k+1) (start m k true) d = true) :
    ¬ packing cycleStep C := by
  apply rejectsJoin_excludes_code_of_endpoints hm hk n.edgeAt _ s d hd hcheck
  intro i hi
  have he : n.edgeAt i ∈ M :=
    (congrArg (fun D => n.edgeAt i ∈ D) n.image_eq).mp
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))
  exact ⟨(hM.1 _ he).1, (hM.1 _ he).2.1⟩

end SevenCycle.TypeTwo
