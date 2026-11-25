import SevenCycle.TypeTwo.Encoding

/-! ## Recovering middle-level membership from a transverse projection -/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry

/-- Restrict one endpoint of a matching to a marked transverse band. The
test reads membership of its twice-projected point in a candidate plane. -/
def seen (pt : ℕ → Tuple 4) (l : Axis) (t : Height) : Mask :=
  pack (fun i => decide (pt i l = t ∨ pt i l = t+1)) 33

def selected (pt : ℕ → Tuple 4) (l : Axis) (r : Tuple 4 → Bool) : Mask :=
  pack (fun i => r (setHeight (pt i) l 0)) 33

/-- Build one candidate mark from the two middle planes of a transverse
projection. The membership predicates can read packed plane data. -/
def markFromPlanes (f : ℕ → Edge) (l : Axis) (t : Height)
    (left right : Tuple 4 → Bool) : Mark :=
  let a := Prod.fst ∘ f
  let b := Prod.snd ∘ f
  let L := seen a l t
  let R := seen b l t
  ⟨L, R, L &&& selected a l left, R &&& selected b l right⟩

private theorem mem_of_cut {S X : Points} (hc : packing cycleStep S) (hX : X ⊆ S)
    {x : Tuple 4} (hx : x ∈ S) {l : Axis} {t : Height} (ht : x l = t ∨ x l = t+1) :
    setHeight x l 0 ∈ stripe X l t ↔ x ∈ X := by
  constructor
  · intro h
    obtain ⟨y, hy, hyt, he⟩ := mem_face.mp h
    have hyx := stripe_injective hc l t (Finset.mem_filter.mpr ⟨hX hy, hyt⟩)
      (Finset.mem_filter.mpr ⟨hx, ht⟩) he
    exact hyx ▸ hy
  · intro h
    exact mem_face.mpr ⟨x, h, ht, rfl⟩

private theorem selected_agrees {S X : Points} {pt : ℕ → Tuple 4} {l : Axis} {t : Height}
    {r : Tuple 4 → Bool} (hc : packing cycleStep S) (hX : X ⊆ S)
    (hmem : ∀ i < 33, pt i ∈ S) (hr : ∀ u, r u ↔ u ∈ stripe X l t) :
    seen pt l t &&& selected pt l r =
      seen pt l t &&& pack (fun i => decide (pt i ∈ X)) 33 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, selected, seen, pack_bit _ _ _ hi]
  by_cases h : pt i l = t ∨ pt i l = t+1
  · simp only [h, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simpa using (hr _).trans (mem_of_cut hc hX (hmem i hi) h)
  · simp [h]

/-- The restrictions are correct for any enumeration of endpoints from the
two support faces. The final join does not use maximality of their pairing. -/
theorem markFromPlanes_of_endpoints {S T X Y : Points} (f : ℕ → Edge)
    (hf : ∀ i < 33, (f i).1 ∈ S ∧ (f i).2 ∈ T)
    (hs : packing cycleStep S) (ht : packing cycleStep T)
    (hX : X ⊆ S) (hY : Y ⊆ T) (l : Axis) (t : Height)
    (left right : Tuple 4 → Bool)
    (hl : ∀ u, left u ↔ u ∈ stripe X l t) (hr : ∀ u, right u ↔ u ∈ stripe Y l t) :
    Realizes (leftOf f X) (rightOf f Y) (markFromPlanes f l t left right) :=
  ⟨selected_agrees hs hX (fun i hi => (hf i hi).1) hl,
    selected_agrees ht hY (fun i hi => (hf i hi).2) hr⟩

/-- Points of S (respectively T) in the transverse band have unique projected
coordinates. Consequently the two prescribed transverse planes recover the
actual X and Y restrictions at every known endpoint of every matching edge. -/
theorem markFromPlanes_realizes {S T X Y : Points} {M : Finset Edge} (hM : Perfect S T M)
    (n : Numbering M) (hs : packing cycleStep S) (ht : packing cycleStep T)
    (hX : X ⊆ S) (hY : Y ⊆ T) (l : Axis) (t : Height)
    (left right : Tuple 4 → Bool)
    (hl : ∀ u, left u ↔ u ∈ stripe X l t) (hr : ∀ u, right u ↔ u ∈ stripe Y l t) :
    Realizes (leftOf n.edgeAt X) (rightOf n.edgeAt Y) (markFromPlanes n.edgeAt l t left right) := by
  have mem {i : ℕ} (hi : i < 33) : n.edgeAt i ∈ M :=
    (congrArg (fun D => n.edgeAt i ∈ D) n.image_eq).mp
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))
  exact markFromPlanes_of_endpoints n.edgeAt (fun i hi =>
    ⟨(hM.1 _ (mem hi)).1,(hM.1 _ (mem hi)).2.1⟩) hs ht hX hY l t left right hl hr

/-- A marked axis and start, and the candidate pairs of plane readers. -/
structure Port where
  axis : Axis
  height : Height
  choices : Array ((Tuple 4 → Bool) × (Tuple 4 → Bool))

def portMarks (f : ℕ → Edge) (p : Port) : Array Mark :=
  p.choices.map fun c => markFromPlanes f p.axis p.height c.1 c.2

def portRows (f : ℕ → Edge) (ports : Array Port) : Array (Array Mark) :=
  ports.map (portMarks f)

/-- This is the obligation of the atlas-domain generator. Each port need only
include one pair reading the true left and right transverse cuts. -/
def CoversCuts (ports : Array Port) (X Y : Points) : Prop :=
  ∀ p ∈ ports, ∃ c ∈ p.choices,
    (∀ u, c.1 u ↔ u ∈ stripe X p.axis p.height) ∧
    (∀ u, c.2 u ↔ u ∈ stripe Y p.axis p.height)

theorem portRows_cover {ports : Array Port} {S T X Y : Points} {M : Finset Edge}
    (hports : CoversCuts ports X Y) (hM : Perfect S T M) (n : Numbering M)
    (hs : packing cycleStep S) (ht : packing cycleStep T) (hX : X ⊆ S) (hY : Y ⊆ T) :
    ∀ i : Fin (portRows n.edgeAt ports).size, ∃ b ∈ (portRows n.edgeAt ports)[i],
      Realizes (leftOf n.edgeAt X) (rightOf n.edgeAt Y) b := by
  intro i
  have row (q : Array Mark) (hq : q ∈ portRows n.edgeAt ports) :
      ∃ b ∈ q, Realizes (leftOf n.edgeAt X) (rightOf n.edgeAt Y) b := by
    obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hq
    obtain ⟨c, hc, hl, hr⟩ := hports p hp
    refine ⟨markFromPlanes n.edgeAt p.axis p.height c.1 c.2, ?_, ?_⟩
    · exact Array.mem_map_of_mem
        (f := fun c : (Tuple 4 → Bool) × (Tuple 4 → Bool) =>
          markFromPlanes n.edgeAt p.axis p.height c.1 c.2) hc
    · exact markFromPlanes_realizes hM n hs ht hX hY _ _ _ _ hl hr
  exact row _ (Array.getElem_mem i.isLt)

/-- When an atlas-domain generator covers the true cuts, rejection by the
packed checker rules out a code with those middle levels. -/
theorem rejectPorts_excludes_middle {ports : Array Port} {m : Frame} {k : Axis} {S T X Y : Points}
    {M : Finset Edge} (hM : Perfect S T M) (n : Numbering M)
    (hs : packing cycleStep S) (ht : packing cycleStep T) (hports : CoversCuts ports X Y)
    (hc : rejectsLayout (portRows n.edgeAt ports) = true) : ¬ TwoMiddle m k S T X Y M :=
  fun h => rejectsLayout_excludes_middle hM n _ hc (portRows_cover hports hM n hs ht h.1 h.2.1) h

end SevenCycle.TypeTwo
