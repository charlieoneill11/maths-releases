import SevenCycle.TypeThree.Normalize
import SevenCycle.Proof.FrameAction

namespace SevenCycle.TypeTwo
open Proof Blueprint Blueprint.SearchSpec

/-- A signed coordinate isometry sends consecutive bands to consecutive bands,
possibly in reverse order. -/
theorem noConsecutive_act {C : Points} (hn : NoConsecutive C) (g : Isometry 4) :
    NoConsecutive (actOnCode g C) := by
  intro k t ht ht'
  let e := Crossings.startEquiv (g.2.1 k) (g.2.2 k)
  obtain ⟨u, hu⟩ := e.surjective t
  obtain ⟨v, hv⟩ := e.surjective (t + 1)
  have inj : Function.Injective (act g) := Function.LeftInverse.injective (Symmetry.undo_act g)
  have mem (a) := Crossings.full_transport C g inj k a
  have hU := (mem u).mp (hu ▸ ht)
  have hV := (mem v).mp (hv ▸ ht')
  have near : ∀ b z u v, Crossings.startEquiv b z v = Crossings.startEquiv b z u + 1 →
      v = u + 1 ∨ u = v + 1 := by decide
  rcases near _ _ u v (hv.trans (congrArg (· + 1) hu.symm)) with h | h
  · exact hn _ u hU (h ▸ hV)
  · exact hn _ v hV (h ▸ hU)

/-- Put an actual type-two anchor at starts zero and two. The first support
is a released atlas representative and the transported frame supplies the
ordered transverse marks consumed by the placement scan. -/
theorem normalize_two (atlas : TypeThree.AtlasComplete) {C : Points} {m : Frame}
    (hc : packing cycleStep C) (hm : Marked m C) (h113 : C.card = 113)
    (hn : NoConsecutive C) (k : Axis) (hk : m.gap k = 2) :
    ∃ D : Points, ∃ n : Frame, packing cycleStep D ∧ Marked n D ∧ n.base 0 = 0 ∧
      n.gap 0 = 2 ∧ D.card = 113 ∧ NoConsecutive D ∧
      ∃ r : Fin atlasPlanes.size, TypeThree.RepresentsBand D 0 0 atlasPlanes[r] := by
  obtain ⟨g, _, hg, hp, _, _, _, r, hr⟩ :=
    Crossings.normalise_full_pair atlas C hc k (m.base k) 2 (hm.2.1 k false)
      (by simpa [start, hk] using hm.2.1 k true)
  have axis (x : Tuple 4) := (hg x).1
  have fields := FrameAction.anchor_fields g k (m.base k) axis
  have inj : Function.Injective (act g) := Function.LeftInverse.injective (Symmetry.undo_act g)
  refine ⟨actOnCode g C, FrameAction.moved g m, hp, FrameAction.marked g hm,
    FrameAction.moved_base_zero g m k axis, ?_, ?_, noConsecutive_act hn g, r, hr.symm⟩
  · change m.gap (g.1 0) = 2
    rwa [fields.1]
  · exact (Finset.card_image_of_injective C inj).trans h113

end SevenCycle.TypeTwo
