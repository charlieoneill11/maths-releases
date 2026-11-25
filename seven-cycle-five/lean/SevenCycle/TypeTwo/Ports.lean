import SevenCycle.TypeTwo.Restrictions
import SevenCycle.Proof.Bitsets

/-! ## Transverse port domains represented by packed three-dimensional cubes -/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry

/-- The packed cube stores the three surviving coordinates in their original order. -/
def Stores (r : Bitsets.Cube) (l : Axis) (W : Points) : Prop :=
  ∀ x : Tuple 4, x l = 0 → (Bitsets.cubeMem r (dropCoord l x) ↔ x ∈ W)

/-- Read one level of a transverse cube into ambient coordinates, keeping
the two erased axes equal to zero in the output. -/
def planeReader (r : Bitsets.Cube) (l k : Axis) (h : Height) (x : Tuple 4) : Bool :=
  decide (x k = 0 ∧ x l = 0) && Bitsets.cubeMem r (dropCoord l (setHeight x k h))

private theorem restore {u : Tuple 4} {k : Axis} {h : Height} (hu : u k = h) :
    setHeight (setHeight u k 0) k h = u := by
  simp [setHeight, ← hu]

theorem planeReader_spec {r : Bitsets.Cube} {l k : Axis} {W : Points}
    (hkl : k ≠ l) (hflat : ∀ x ∈ W, x l = 0) (hr : Stores r l W) (h : Height) (x : Tuple 4) :
    planeReader r l k h x ↔ x ∈ plane W k h := by
  simp only [planeReader, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hxk,hxl⟩, hmem⟩
    have hz : setHeight x k h l = 0 := by simpa [setHeight, hkl.symm] using hxl
    apply mem_face.mpr
    exact ⟨setHeight x k h, (hr _ hz).mp hmem, by simp [setHeight], by
      simp [setHeight, ← hxk]⟩
  · intro hx
    obtain ⟨u, hu, huk, rfl⟩ := mem_face.mp hx
    rw [restore huk]
    refine ⟨⟨by simp [setHeight], ?_⟩, (hr u (hflat u hu)).mpr hu⟩
    simpa [setHeight, hkl.symm] using hflat u hu

structure PackedPort where
  axis : Axis
  height : Height
  cubes : Array Bitsets.Cube

/-- Read the two inner levels of each candidate transverse projection. -/
def readPort (k : Axis) (inner outer : Height) (p : PackedPort) : Port :=
  ⟨p.axis, p.height, p.cubes.map fun r =>
    (planeReader r p.axis k inner, planeReader r p.axis k outer)⟩

/-- A cube domain covers a port if it contains a representation of the
actual transverse projection. Duplicate cubes and additional candidates are harmless. -/
def CoversPorts (C : Points) (k : Axis) (ports : Array PackedPort) : Prop :=
  ∀ p ∈ ports, p.axis ≠ k ∧ ∃ r ∈ p.cubes, Stores r p.axis (stripe C p.axis p.height)

theorem readPorts_cover {C : Points} {k : Axis} {ports : Array PackedPort}
    (hports : CoversPorts C k ports) (inner outer : Height) :
    CoversCuts (ports.map (readPort k inner outer)) (plane C k inner) (plane C k outer) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Array.mem_map.mp hq
  obtain ⟨hne,r,hr,hw⟩ := hports p hp
  have flat : ∀ u ∈ stripe C p.axis p.height, u p.axis = 0 := by
    intro u hu
    obtain ⟨z,_,_,rfl⟩ := mem_face.mp hu
    simp [setHeight]
  have spec (s : Height) (u : Tuple 4) :
      planeReader r p.axis k s u ↔ u ∈ stripe (plane C k s) p.axis p.height := by
    rw [show stripe (plane C k s) p.axis p.height = plane (stripe C p.axis p.height) k s from
      face_comm C hne.symm (fun z => z = s) (fun z => z = p.height ∨ z = p.height+1)]
    exact planeReader_spec hne.symm flat hw s u
  exact ⟨_, Array.mem_map_of_mem (f := fun r =>
    (planeReader r p.axis k inner, planeReader r p.axis k outer)) hr, spec inner, spec outer⟩

/-- Complete packed transverse domains cannot reject a true type-two layout
under any numbering of any perfect matching. -/
theorem rejectsPacked_excludes_code
    (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33)
    {C : Points} {k : Axis} {m : Frame} {M : Finset Edge} (hm : Marked m C)
    (hk : m.gap k = 2) (h113 : C.card = 113) (hn : NoConsecutive C)
    (hM : Perfect (projections m C k false) (projections m C k true) M) (n : Numbering M)
    (ports : Array PackedPort) (hp : CoversPorts C k ports)
    (hcheck : rejectsLayout (portRows n.edgeAt
      (ports.map (readPort k (m.base k+1) (start m k true)))) = true) :
    ¬ packing cycleStep C := by
  intro hc
  have hs := stripe_packing hc k (start m k false)
  have ht := stripe_packing hc k (start m k true)
  exact rejectPorts_excludes_middle hM n hs ht (readPorts_cover hp _ _) hcheck
    (middle_retains_113 h3 hc hm hk h113 hn M hM)

end SevenCycle.TypeTwo
