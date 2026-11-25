import SevenCycle.Adjacent.MixedCommon

namespace SevenCycle.Adjacent.MixedCommon

open Proof Blueprint Blueprint.SearchSpec SlabJoin SlabReconstruction
open MixedSlabs (Profile)

private def offset (cs : Centers) : Tuple 4 := Fin.cons (α := fun _ => Height) 1 (fun j => cs.get j)

private def sortedAction (g : Isometry 4) (cs : Centers) (e : Equiv.Perm Axis) : Isometry 4 :=
  (e.symm.trans g.1, fun j => g.2.1 (e.symm j), fun j => g.2.2 (e.symm j) - offset cs (e.symm j))

private theorem sorted_at (g : Isometry 4) (cs : Centers) (e : Equiv.Perm Axis) (x : Tuple 4) (j : Axis) :
    act (sortedAction g cs e) x (e j) = CommonFrame.View g cs x j := by
  simp only [act,sortedAction,Equiv.trans_apply,Equiv.symm_apply_apply,CommonFrame.View,center,offset]
  rw [add_sub_assoc]

theorem frame_eq {m n : Frame} (gap : ∀ j, m.gap j = n.gap j) (base : ∀ j, m.base j = n.base j) : m = n := by
  cases m; cases n; congr <;> funext i <;> first | exact gap i | exact base i

/-- Incorporate the coordinate sorting and later-start translations into a single isometry. -/
theorem atAnchor_of_local {C : Points} {m : Frame} {k : Axis} {p : Profile} {rows : Array String}
    (g : Isometry 4) (cs : Centers) (o : AxisOrder) (e : Equiv.Perm Axis)
    (anchor : g.1 0 = k) (e0 : e 0 = 0) (eo : ∀ j : Axis, o[j] = e j)
    (gaps : ∀ j, m.gap (g.1 j) = (p.get (e j)).val)
    (starts : ∀ j, Fin.cons (α := fun _ => Height) 1 (fun l => cs.get l) j = start (FrameAction.moved g m) j true)
    (r : String) (hr : r ∈ rows)
    (hit : (normSlab (actOnCode g C)).image (center cs) = (rowPoints r).image (signedAction o 0)) :
    AtAnchor C m p rows k := by
  let f := sortedAction g cs e
  have ez : e.symm 0 = 0 := e.symm_apply_eq.mpr e0.symm
  have fzero : f.1 0 = k := by simp [f,sortedAction,ez,anchor]
  refine ⟨f,fzero,frame_eq ?_ ?_,r,hr,?_⟩
  · intro j
    change m.gap (g.1 (e.symm j)) = (p.get j).val
    simpa using gaps (e.symm j)
  · intro j
    let i := e.symm j
    have hgap : (m.gap (g.1 i) : Height) = p.get j := by
      rw [gaps, show e i = j from e.apply_symm_apply j]
      exact ZMod.natCast_zmod_val (show Height from p.get j)
    have d (b : Bool) (t a h : Height) :
        Crossings.startValue b (t-h) a = Crossings.startValue b t a - h := by
      cases b <;> simp [Crossings.startValue,add_sub_assoc]
    change Crossings.startValue (g.2.1 i) (g.2.2 i - offset cs i)
      (start m (g.1 i) (g.2.1 i)) = -(show Height from p.get j)
    rw [d]
    change (FrameAction.moved g m).base i - offset cs i = _
    rw [show offset cs i = start (FrameAction.moved g m) i true from starts i]
    simp only [start,if_true]
    change (FrameAction.moved g m).base i - ((FrameAction.moved g m).base i + (m.gap (g.1 i) : Height)) = _
    rw [hgap]; simp
  · let permute := signedAction o 0
    have value (x : Tuple 4) (j : Axis) : permute x j = x (e j) := by simp [permute,signedAction,eo]
    have inj : Function.Injective permute := by
      intro x y he
      funext j
      simpa only [value,Equiv.apply_symm_apply] using congrFun he (e.symm j)
    have matchx (x : Tuple 4) : permute (act f x) = CommonFrame.View g cs x := by
      funext j
      rw [value]
      exact sorted_at g cs e x j
    have window (x : Tuple 4) : inThree 0 (act f x) ↔ inThree 0 (CommonFrame.View g cs x) := by
      have h := sorted_at g cs e x 0
      rw [e0] at h
      change act f x 0 = CommonFrame.View g cs x 0 at h
      simp only [inThree,h]
    ext x
    constructor
    · intro hx
      obtain ⟨hx,hi⟩ := Finset.mem_filter.mp hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      have im := (CommonFrame.mem_local cs g C _).mpr ⟨z,hz,(window z).mp hi,rfl⟩
      rw [hit] at im
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp im
      have eq := inj (he.trans (matchx z).symm)
      exact eq ▸ hw
    · intro hx
      have im : permute x ∈ (normSlab (actOnCode g C)).image (center cs) :=
        hit ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩
      obtain ⟨z,hz,hi,he⟩ := (CommonFrame.mem_local cs g C _).mp im
      have eq := inj ((matchx z).trans he)
      rw [← eq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,(window z).mpr hi⟩

end SevenCycle.Adjacent.MixedCommon
