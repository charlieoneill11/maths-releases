import SevenCycle.Proof.Matching
import SevenCycle.Proof.Frame

/-! ## Lifting the three-dimensional matching to flat ambient faces -/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec

private theorem flat_band {S : Points} {k : Axis} (hs : Face33 k S) : band S k 0 = S :=
  Finset.filter_true_of_mem fun x hx => Or.inl (hs.2.2 x hx)

private theorem flat_inj {S : Points} {k : Axis} (hs : Face33 k S) :
    Set.InjOn (dropCoord k) S := by
  have h : Set.InjOn (dropCoord k) ↑(band S k 0) := (Bands.band_projection hs.2.1 k 0).1
  simpa [flat_band hs] using h

private theorem flat_pack {S : Points} {k : Axis} (hs : Face33 k S) :
    packing cycleStep (S.image (dropCoord k)) := by
  have h : packing cycleStep ((band S k 0).image (dropCoord k)) := (Bands.band_projection hs.2.1 k 0).2
  simpa [flat_band hs] using h

private noncomputable def flatEquiv {S : Points} {k : Axis} (hs : Face33 k S) :
    ↥S ≃ ↥(S.image (dropCoord k)) :=
  Equiv.ofBijective (fun x => ⟨dropCoord k x.val, Finset.mem_image_of_mem _ x.property⟩)
    ⟨fun x y h => Subtype.ext (flat_inj hs x.property y.property (congrArg Subtype.val h)),
     fun y => by
       obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.property
       exact ⟨⟨x,hx⟩, Subtype.ext hxy⟩⟩

private theorem lift_edge {x y : Tuple 4} (k : Axis) (hx : x k = 0) (hy : y k = 0)
    (edge : conflictEdge (dropCoord k x) (dropCoord k y)) : x = y ∨ conflict cycleStep x y := by
  rcases edge with he | ⟨hne,hc⟩
  · left
    apply funext
    exact (Fin.forall_iff_succAbove k).mpr ⟨hx.trans hy.symm, fun j => congrFun he j⟩
  · right
    refine ⟨fun h => hne (congrArg (dropCoord k) h), (Fin.forall_iff_succAbove k).mpr ⟨?_, hc⟩⟩
    simp [cycleStep, hx, hy]

/-- Any two maximum codes in the same flat three-dimensional face have a
perfect matching when regarded as ambient words with the erased coordinate zero. -/
theorem perfect_faces (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33)
    {k : Axis} {S T : Points} (hs : Face33 k S) (ht : Face33 k T) :
    ∃ M, Perfect S T M := by
  obtain ⟨em, edges⟩ := Matching.perfect_matching h3 _ _ (flat_pack hs) (flat_pack ht)
    ((Finset.card_image_of_injOn (flat_inj hs)).trans hs.1)
    ((Finset.card_image_of_injOn (flat_inj ht)).trans ht.1)
  let e := ((flatEquiv hs).trans em).trans (flatEquiv ht).symm
  have match_edge (x : ↥S) : x.val = (e x).val ∨ conflict cycleStep x.val (e x).val := by
    apply lift_edge k (hs.2.2 x x.property) (ht.2.2 _ (e x).property)
    have h : dropCoord k (e x).val = (em (flatEquiv hs x)).val :=
      congrArg Subtype.val ((flatEquiv ht).apply_symm_apply _)
    rw [h]
    exact edges (flatEquiv hs x)
  let M := S.attach.image fun x => (x.val, (e x).val)
  have mem (x y : Tuple 4) : (x,y) ∈ M ↔ ∃ hx : x ∈ S, (e ⟨x,hx⟩).val = y := by
    constructor
    · intro h
      obtain ⟨u, _, hxy⟩ := Finset.mem_image.mp h
      obtain rfl : u.val = x := congrArg Prod.fst hxy
      exact ⟨u.property, congrArg Prod.snd hxy⟩
    · rintro ⟨hx, rfl⟩
      exact Finset.mem_image_of_mem _ (S.mem_attach ⟨x,hx⟩)
  refine ⟨M, ?_, ?_, ?_⟩
  · rintro ⟨x,y⟩ h
    obtain ⟨hx, rfl⟩ := (mem x y).mp h
    exact ⟨hx, (e ⟨x,hx⟩).property, match_edge ⟨x,hx⟩⟩
  · intro x hx
    refine ⟨(e ⟨x,hx⟩).val, (mem _ _).mpr ⟨hx, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨_, hz⟩ := (mem _ _).mp hz
    exact hz.symm
  · intro y hy
    let v : ↥T := ⟨y,hy⟩
    refine ⟨(e.symm v).val, (mem _ _).mpr ⟨(e.symm v).property, congrArg Subtype.val (e.apply_symm_apply v)⟩, ?_⟩
    intro z hz
    obtain ⟨hzS, hzy⟩ := (mem _ _).mp hz
    exact congrArg Subtype.val (e.eq_symm_apply.mpr (Subtype.ext hzy) : (⟨z,hzS⟩ : ↥S) = e.symm v)

end SevenCycle.TypeTwo
