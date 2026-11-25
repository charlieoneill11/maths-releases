import SevenCycle.Adjacent.LocalView
import SevenCycle.Adjacent.MixedSlabs
import SevenCycle.Proof.FrameAction

/-! Compare normalized mixed slabs in one frame. Reversing an axis of gap d
acts by x ↦ 1-d-x, which interchanges its two marked bands. -/

namespace SevenCycle.Adjacent.MixedCommon

open Proof Blueprint Blueprint.SearchSpec SlabJoin SlabReconstruction
open MixedSlabs (Profile Covers)

def physicalFrame (p : Profile) : Frame :=
  ⟨fun j => (p.get j).val, fun j => -(show Height from p.get j)⟩

def AtAnchor (C : Points) (m : Frame) (p : Profile) (rows : Array String) (k : Axis) : Prop :=
  ∃ g : Isometry 4, g.1 0 = k ∧ FrameAction.moved g m = physicalFrame p ∧
    ∃ r ∈ rows, (actOnCode g C).filter (inThree 0) = rowPoints r

private def order (g h : Isometry 4) : AxisOrder := Vector.ofFn fun j => h.1.symm (g.1 j)
private def signs (g h : Isometry 4) := CommonFrame.signCode fun j => (g.2.1 j) ^^ (h.2.1 ((order g h)[j]))

private theorem sameSlot (a b : Bool) (d base t u x : Height)
    (ha : Crossings.startValue a t (if a then base+d else base) = -d)
    (hb : Crossings.startValue b u (if b then base+d else base) = -d) :
    (if a ^^ b then 1-d-((if b then -x else x)+u) else (if b then -x else x)+u) =
      (if a then -x else x)+t := by
  have shift : ∀ (neg : Bool) (d base t : Height),
      Crossings.startValue neg t (if neg then base+d else base) = -d →
        t = if neg then base+1 else -d-base := by decide +kernel
  rw [shift _ _ _ _ ha,shift _ _ _ _ hb]
  clear ha hb shift t u
  revert a b d base x
  decide +kernel

private theorem match_views (m : Frame) (p : Profile) (g h : Isometry 4)
    (hg : FrameAction.moved g m = physicalFrame p) (hh : FrameAction.moved h m = physicalFrame p)
    (x : Tuple 4) :
    MixedSlabs.action p (order g h) (signs g h).val (act h x) = act g x := by
  funext i
  let j := (order g h)[i]
  have hj : h.1 j = g.1 i := by simp [j,order]
  have ggap := congrArg (fun m : Frame => m.gap i) hg
  have hgap := congrArg (fun m : Frame => m.gap j) hh
  change m.gap (g.1 i) = (p.get i).val at ggap
  change m.gap (h.1 j) = (p.get j).val at hgap
  have dp : p.get j = p.get i := Fin.ext ((hgap.symm.trans (congrArg m.gap hj)).trans ggap)
  have castg : (m.gap (g.1 i) : Height) = p.get i := by rw [ggap]; exact ZMod.natCast_zmod_val (show Height from p.get i)
  have castH : (m.gap (h.1 j) : Height) = p.get i := by rw [hj,castg]
  have gm := congrArg (fun m : Frame => m.base i) hg
  have hm := congrArg (fun m : Frame => m.base j) hh
  change Crossings.startValue (g.2.1 i) (g.2.2 i) (if g.2.1 i then _+_ else _) = -(show Height from p.get i) at gm
  change Crossings.startValue (h.2.1 j) (h.2.2 j) (if h.2.1 j then _+_ else _) = -(show Height from p.get j) at hm
  rw [castg] at gm
  rw [castH,hj,dp] at hm
  change (if (signs g h).val.testBit i then 1-(show Height from p.get i)-act h x j else act h x j) = _
  rw [signs, CommonFrame.sign_bit]
  unfold act
  rw [hj]
  exact sameSlot _ _ _ _ _ _ _ gm hm

/-- Choosing any one anchored normalization identifies a common normalized
code. Each other active slab is an allowed transform of its local row. -/
theorem coverage {C : Points} {m : Frame} {p : Profile} {rows : Array String}
    (g : Isometry 4) (gm : FrameAction.moved g m = physicalFrame p)
    (gRow : ∃ r ∈ rows, (actOnCode g C).filter (inThree 0) = rowPoints r)
    (localRows : ∀ k, m.gap k = 1 → AtAnchor C m p rows k)
    (i : Axis) (active : p.get i = 1) :
    Covers p rows i ((actOnCode g C).filter (inThree i)) := by
  by_cases atZero : i = 0
  · subst i
    obtain ⟨r,hr,he⟩ := gRow
    refine ⟨r,hr,(identityOrder,0),by simp [MixedSlabs.transforms],?_⟩
    rw [he]
    have ident : MixedSlabs.action p identityOrder 0 = id := by
      funext x k
      fin_cases k <;> rfl
    rw [ident,Finset.image_id]
  · have rawgap := congrArg (fun m : Frame => m.gap i) gm
    change m.gap (g.1 i) = (p.get i).val at rawgap
    obtain ⟨h,ha,hm,r,hr,he⟩ := localRows (g.1 i) (by simpa [active] using rawgap)
    let o := order g h
    let s := signs g h
    have perm (j : Axis) : o[j] = h.1.symm (g.1 j) := by simp [o,order]
    have normal : o[i] = 0 := (perm _).trans (h.1.symm_apply_eq.mpr ha.symm)
    have inj : Function.Injective (fun j : Axis => o[j]) := by
      intro j k e
      simpa only [perm,Equiv.apply_eq_iff_eq] using e
    have pres (j : Axis) : p.get j = p.get o[j] := by
      have ggap := congrArg (fun M : Frame => M.gap j) gm
      have hgap := congrArg (fun M : Frame => M.gap o[j]) hm
      change m.gap (g.1 j) = (p.get j).val at ggap
      change m.gap (h.1 o[j]) = (p.get o[j]).val at hgap
      rw [show h.1 o[j] = g.1 j by rw [perm,Equiv.apply_symm_apply]] at hgap
      exact Fin.ext (ggap.symm.trans hgap)
    refine ⟨r,hr,(o,s.val),MixedSlabs.transform_mem p i o s inj normal pres (fun e => (atZero e).elim),?_⟩
    rw [← he]
    have mapping := match_views m p g h gm hm
    have window (x : Tuple 4) : inThree i (act g x) ↔ inThree 0 (act h x) := by
      rw [← mapping]
      have zz : ∀ (b : Bool) (z : Height), let v := if b then 1-1-z else z
        (v = 6 ∨ v = 0 ∨ v = 1) ↔ (z = 6 ∨ z = 0 ∨ z = 1) := by decide
      change (let v := if s.val.testBit i then 1-(show Height from p.get i)-act h x o[i] else act h x o[i]; _) ↔ _
      have h0 : (order g h)[i] = 0 := normal
      simpa only [inThree,MixedSlabs.action,active,h0] using zz (s.val.testBit i) (act h x 0)
    ext w
    constructor
    · intro hw
      obtain ⟨hin,hw⟩ := Finset.mem_filter.mp hw
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hin
      exact Finset.mem_image.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,(window x).mp hw⟩,mapping x⟩
    · intro hw
      obtain ⟨_,hh,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hin,hwin⟩ := Finset.mem_filter.mp hh
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hin
      rw [show MixedSlabs.action p o s.val (act h x) = act g x from mapping x]
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,(window x).mpr hwin⟩

end SevenCycle.Adjacent.MixedCommon
