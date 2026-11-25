import SevenCycleRuntime.BandStage
import SevenCycle.Adjacent.BandCounts
import SevenCycle.Adjacent.BandDomains
import SevenCycle.Adjacent.MarkedScan
import SevenCycle.Adjacent.Visible

namespace SevenCycle.Adjacent.BandStage
open Blueprint Blueprint.SearchSpec Proof Bitsets
open BandJoin (Prefix Port)

private theorem physical_ports (m : Frame) (hm : ValidFrame m) (s t v : Cube) :
    ports s t v (Scan.gapsOf m) (Scan.centersOf m) =
    BandJoin.physicalPorts m (counts s t v (Scan.centersOf m)) := by
  unfold ports BandJoin.physicalPorts
  congr 1
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    exact (Scan.frame_starts m ⟨i,hi⟩).2
  · apply Vector.ext
    intro i hi
    let a : Fin 3 := ⟨i,hi⟩
    simp only [Vector.getElem_map, Scan.gapsOf, Vector.getElem_ofFn]
    change (m.gap a.succ) % 7 = m.gap a.succ
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (hm a.succ).2 (by decide))

private theorem start_mem (m : Frame) (a : Fin 3) (b : Bool) :
    (a, start m a.succ b) ∈ ScanFused.ports (Scan.gapsOf m) (Scan.centersOf m) := by
  have h := ScanFused.port_start (Scan.gapsOf m) (Scan.centersOf m) a b
  cases b
  · change (a, (Scan.centersOf m).get a - (Scan.gapsOf m).get a) ∈ _ at h
    rwa [(Scan.frame_starts m a).2] at h
  · change (a, (Scan.centersOf m).get a) ∈ _ at h
    rwa [(Scan.frame_starts m a).1] at h

private theorem lookup (atlas : Contacts.AtlasComplete) (needed : Prefix → Bool)
    {C : Points} {s t u v : Cube} {gaps cs : Scan.Marks} (p : Port)
    (hc : packing cycleStep C) (hf : p.start ∈ fullStarts C p.axis.succ)
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1)
    (hv : cubeSet v = (cubeSet u).filter (ScanFused.covered gaps cs ·))
    (hw : (p.axis,p.start) ∈ ScanFused.ports gaps cs) (hn : needed (BandJoin.request s t v p)) :
    ∃ w ∈ (BandJoin.indexPrefixes orbitImages needed atlasPlanes).getD (BandJoin.request s t v p) #[],
      TypeThree.RepresentsBand C p.axis.succ p.start w := by
  obtain ⟨hi,code⟩ := Bands.band_projection hc p.axis.succ p.start
  have size : (projectedBand C p.axis.succ p.start).card = 33 :=
    (Finset.card_image_of_injOn hi).trans (Finset.mem_filter.mp hf).2
  obtain ⟨q,g,eq⟩ := atlas _ code size
  obtain ⟨w,hm,hrep⟩ := orbitImages_complete g atlasPlanes[q]
  have rep : TypeThree.RepresentsBand C p.axis.succ p.start w := hrep.trans eq.symm
  have key : BandJoin.prefixOf w = BandJoin.request s t v p := by
    rw [BandJoin.prefix_of_band hs ht hu rep]
    simp only [BandJoin.request, ScanFused.visible_cuts hv hw]
  refine ⟨w,?_,rep⟩
  rw [← key] at hn ⊢
  exact BandJoin.index_covers needed atlasPlanes (Array.getElem_mem q.isLt) hm hn

private theorem in_domains (idx : BandJoin.Index) (ps : BandJoin.Ports) (f : Port → Prefix)
    (i : Fin 6) (w : Cube) (hw : w ∈ idx.getD (f (ps.get i)) #[]) :
    w ∈ ((ps.map f).map (fun k => idx.getD k #[])).get i := by
  change w ∈ ((ps.map f).map (fun k => idx.getD k #[]))[i.val]
  rw [Vector.getElem_map, Vector.getElem_map]
  exact hw

/-- Sparse hints can only skip the join filter. With every key indexed,
the physical six bands survive the exact join and centre-capacity tests. -/
theorem survives_sound (atlas : Contacts.AtlasComplete) (needed : Prefix → Bool)
    {C : Points} {m : Frame} {s t u visible : Cube} (hc : packing cycleStep C) (hm : Marked m C)
    (hb : m.base 0 = 0) (hg : m.gap 0 = 1)
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1)
    (hv : cubeSet visible = (cubeSet u).filter (ScanFused.covered (Scan.gapsOf m) (Scan.centersOf m) ·)) :
    survives needed (BandJoin.indexPrefixes orbitImages needed atlasPlanes)
      s t (Scan.gapsOf m) (Scan.centersOf m) visible = true := by
  let idx := BandJoin.indexPrefixes orbitImages needed atlasPlanes
  let nums := counts s t visible (Scan.centersOf m)
  let ps := BandJoin.physicalPorts m nums
  let keys := ps.map (BandJoin.request s t visible)
  let ds := keys.map fun k => idx.getD k #[]
  unfold survives
  rw [physical_ports m hm.1]
  change (!keys.toArray.all needed || BandJoin.canJoin ps ds) = true
  by_cases hon : keys.toArray.all needed = true
  · apply Bool.or_eq_true_iff.mpr
    apply Or.inr
    apply BandJoin.actual_join C m hc hm hb hg nums ds
    · intro i
      let p := ps.get i
      have atPort := BandJoin.port_get m nums i
      have hf : p.start ∈ fullStarts C p.axis.succ := by
        change (ps.get i).start ∈ fullStarts C (ps.get i).axis.succ
        rw [show ps.get i = _ from atPort]
        exact hm.2.1 _ _
      have hw : (p.axis,p.start) ∈ ScanFused.ports (Scan.gapsOf m) (Scan.centersOf m) := by
        change ((ps.get i).axis,(ps.get i).start) ∈ _
        rw [show ps.get i = _ from atPort]
        exact start_mem m _ _
      have key : keys[i.val] = BandJoin.request s t visible p := Vector.getElem_map ..
      have hn := Array.all_eq_true_iff_forall_mem.mp hon _ (Array.getElem_mem (xs := keys.toArray)
        (i := i.val) (by simp))
      change needed keys[i.val] = true at hn
      rw [key] at hn
      obtain ⟨w, hwmem, rep⟩ := lookup atlas needed p hc hf hs ht hu hv hw hn
      refine ⟨w,?_,?_⟩
      · exact in_domains idx ps (BandJoin.request s t visible) i w hwmem
      · change TypeThree.RepresentsBand C (ps.get i).axis.succ (ps.get i).start w at rep
        rw [show ps.get i = _ from atPort] at rep
        exact rep
    · intro a _
      rw [Adjacent.slab_eq hc hg]
      have cen := (Scan.frame_starts m a).1
      let c := (Scan.centersOf m).get a
      have upper := BandCounts.known_upper hc hb hg hs ht hu a c
      have sl := ScanFused.visible_level hv a
      have eq := BandCounts.known_eq_of_slice s t visible u a c (fun x hx => by
        have mem := Finset.ext_iff.mp sl x
        have hxc : x a = (Scan.centersOf m).get a := hx
        simpa only [Finset.mem_filter, hxc, and_true] using mem)
      change _ ≤ (Vector.ofFn fun k : Fin 3 => BandCounts.known s t visible k ((Scan.centersOf m).get k)).get a
      change _ ≤ (Vector.ofFn fun k : Fin 3 => BandCounts.known s t visible k ((Scan.centersOf m).get k))[a.val]
      rw [Vector.getElem_ofFn, eq]
      simpa only [c, cen] using upper
  · rw [Bool.eq_false_iff.mpr hon]; rfl

end SevenCycle.Adjacent.BandStage
