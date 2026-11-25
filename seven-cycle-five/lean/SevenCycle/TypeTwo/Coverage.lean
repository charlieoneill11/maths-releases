import SevenCycle.TypeTwo.Search
import SevenCycle.TypeTwo.MiddleIndex

namespace SevenCycle.TypeTwo.Search

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry
open Bitsets (Cube)

private theorem anchor_rep {r : Cube} {C : Points} {t : Height} (h : TypeThree.RepresentsBand C 0 t r) :
    anchorFace r = stripe C 0 t := by
  ext x
  constructor
  · intro hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    apply (stores_of_rep h _ (by simp)).mp
    simpa [dropCoord] using (Bitsets.mem_cubeSet _ _).mp hu
  · intro hx
    have hx0 : x 0 = 0 := by
      obtain ⟨y,_,_,rfl⟩ := mem_face.mp hx
      simp [setHeight]
    refine Finset.mem_image.mpr ⟨dropCoord 0 x, (Bitsets.mem_cubeSet _ _).mpr ((stores_of_rep h x hx0).mpr hx),?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hx0.symm
    · simp [dropCoord]

private theorem actual_reads {r : Cube} {C : Points} {a : Fin 3} {t : Height}
    (h : TypeThree.RepresentsBand C a.succ t r) (z : Height) (u : Tuple 4) :
    planeReader r a.succ 0 z u ↔ u ∈ stripe (plane C 0 z) a.succ t := by
  rw [show stripe (plane C 0 z) a.succ t = plane (stripe C a.succ t) 0 z from
    face_comm C (Fin.succ_ne_zero a).symm (fun v => v=z) (fun v => v=t ∨ v=t+1)]
  refine planeReader_spec (Fin.succ_ne_zero a).symm (fun v hv => ?_) (stores_of_rep h) z u
  obtain ⟨v,_,_,rfl⟩ := mem_face.mp hv
  simp [setHeight]

/-- For each marked height the table contains the two inner planes of some
representation of the actual transverse cube. -/
def CoversMiddle (C : Points) (idx : Mid.Index) (s t : Cube) (p : Placement) : Prop :=
  ∀ c ∈ (Mid.contacts p).toArray, ∃ w : Cube, TypeThree.RepresentsBand C c.1.succ c.2 w ∧
    (w[1],w[2]) ∈ idx.getD ((grid s)[c.1][c.2],(grid t)[c.1][c.2]) #[]

theorem reject_false (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33)
    {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C)
    (hb : m.base 0 = 0) (hg : m.gap 0 = 2) (h113 : C.card = 113) (hn : NoConsecutive C)
    {idx : Mid.Index} {s t : Cube} (hs : TypeThree.RepresentsBand C 0 0 s)
    (ht : TypeThree.RepresentsBand C 0 2 t) {p : Placement} (cover : CoversMiddle C idx s t p)
    {xs ys : Graph.Sites} (hv : Graph.valid s t xs ys) :
    Mid.reject (Mid.rows idx (grid s) (grid t) xs ys) p = false := by
  have hstart : start m 0 true = 2 := by simp [start,hb,hg]
  have hs' : anchorFace s = projections m C 0 false := by simpa [projections,start,hb] using anchor_rep hs
  have ht' : anchorFace t = projections m C 0 true := by simpa only [projections,hstart] using anchor_rep ht
  have sm := face33 hc (hm.2.1 0 false)
  have tm := face33 hc (hm.2.1 0 true)
  let f := paired xs ys
  let M := (Finset.range 33).image f
  obtain ⟨hM, n, he⟩ := valid_matching hv (hs' ▸ sm.1) (ht' ▸ tm.1)
  rw [hs', ht'] at hM
  have H := middle_retains_113 h3 hc hm hg h113 hn M hM
  have h1 : m.base 0 + 1 = 1 := by simp [hb]
  rw [h1,hstart] at H
  apply Bool.eq_false_iff.mpr
  intro bad
  apply (rejectsLayout_excludes_middle hM n _ bad _ H)
  intro i
  let cs := (Mid.contacts p).toArray
  have hi : i.val < cs.size := by simpa [cs] using i.isLt
  let c := cs[i.val]
  obtain ⟨r,hr, hmem⟩ := cover c (Array.getElem_mem hi)
  let mark := markFromPlanes f c.1.succ c.2 (planeReader r c.1.succ 0 1) (planeReader r c.1.succ 0 2)
  refine ⟨mark,?_,?_⟩
  · let rows := Mid.rows idx (grid s) (grid t) xs ys
    change mark ∈ (cs.map (fun x => rows[x.1][x.2]))[i.val]
    rw [Array.getElem_map]
    change mark ∈ (rows[c.1.val])[c.2.val]
    simp only [rows, Mid.rows, Vector.getElem_ofFn]
    exact Mid.row_marks xs ys r c.1 c.2 _ hmem
  · have hr' := markFromPlanes_realizes hM n sm.2.1 tm.2.1 H.1 H.2.1
      c.1.succ c.2 _ _ (actual_reads hr 1) (actual_reads hr 2)
    change Realizes _ _ (markFromPlanes f _ _ _ _)
    change n.edgeAt = f at he
    rw [he] at hr' ⊢
    exact hr'

theorem filterMiddle_mem {idx : Mid.Index} {s t : Cube} {ps : Array Placement} {p : Placement}
    (hp : p ∈ ps) (hn : ∀ xs ys, Graph.valid s t xs ys →
      Mid.reject (Mid.rows idx (grid s) (grid t) xs ys) p = false) :
    p ∈ filterMiddle idx s t (grid s) (grid t) ps := by
  cases hx : Mid.sites s with
  | none => simpa only [filterMiddle,hx] using hp
  | some xs =>
    cases hy : Mid.sites t with
    | none => simpa only [filterMiddle,hx,hy] using hp
    | some ys =>
      cases hh : Graph.propose xs ys with
      | none => simpa only [filterMiddle,hx,hy,hh] using hp
      | some z =>
        obtain ⟨ls,rs⟩ := z
        by_cases hv : Graph.valid s t ls rs
        · simp only [filterMiddle,hx,hy,hh,hv,if_true,Id.run,pure]
          exact Array.mem_filter.mpr ⟨hp,by simp [hn _ _ hv]⟩
        · simpa only [filterMiddle,hx,hy,hh,Bool.eq_false_iff.mpr hv,if_false] using hp

theorem partners_mem {idx : Mid.Index} {x y : UInt64} {v : Mid.MiddlePair} (hv : v ∈ idx.getD (x,y) #[]) :
    y ∈ (Mid.partners idx).getD x #[] := by
  have hkey : (x,y) ∈ idx := by
    by_contra h
    simp [Std.HashMap.getD_eq_getD_getElem?,Std.HashMap.getElem?_eq_none h] at hv
  apply Planar.fold_keeps idx.keysArray Planar.appendPartner {} (fun p : Planar.PartnerTable => y ∈ p.getD x #[])
    (fun k => k = (x,y)) _ (Or.inr ⟨_,Std.HashMap.mem_keysArray.mpr hkey,rfl⟩)
  intro tb k h
  by_cases eq : k.1 = x
  · rcases h with hp | rfl <;> simp_all [Planar.appendPartner, Std.HashMap.getD_eq_getD_getElem?, Array.mem_push]
  · rcases h with hp | rfl
    · simpa only [Planar.appendPartner, Std.HashMap.getD_alter, beq_iff_eq, eq, if_false] using hp
    · exact False.elim (eq rfl)

private theorem contact_mem (p : Placement) (a : Fin 3) (t : Fin 7)
    (h : t ∈ ({p[a].first,p[a].last} : Finset (Fin 7))) : (a,t) ∈ (Mid.contacts p).toArray := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl <;> fin_cases a <;> simp [Mid.contacts]

private theorem pack_picks (p : Placement) : #v[p[0],p[1],p[2]] = p := by
  ext i hi
  have : i < 3 := hi
  obtain h | h | h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  all_goals subst i; rfl

theorem forTarget_retains {ss : Array Cube} (i : Fin ss.size) {t : Cube} {p : Placement} {idx : Mid.Index}
    (hyes : ∀ a : Fin 3, ∀ j ∈ ({p[a].first,p[a].last} : Finset (Fin 7)),
      (grid t)[a][j] ∈ (Mid.partners idx).getD (grid ss[i])[a][j] #[])
    (hm : ∀ xs ys, Graph.valid ss[i] t xs ys → Mid.reject (Mid.rows idx (grid ss[i]) (grid t) xs ys) p = false) :
    (⟨ss[i],t,p⟩ : Layout) ∈ forTarget idx ss (Planar.candidateIndex (Mid.partners idx) (ss.map grid)) t := by
  let gs := ss.map grid
  let j : Fin gs.size := ⟨i.val,by simp [gs]⟩
  have hg : gs[j] = grid ss[i] := Array.getElem_map ..
  have hh : ∀ a : Fin 3, ∀ b ∈ ({p[a].first,p[a].last} : Finset (Fin 7)),
      (grid t)[a][b] ∈ (Mid.partners idx).getD gs[j][a][b] #[] := hg ▸ hyes
  let ci := Planar.candidateIndex (Mid.partners idx) gs
  have hbit := Planar.eligibleSources_retains (Mid.partners idx) gs j (grid t) p hh
  have hplace : p ∈ Planar.placements ci i.val (grid t) := by
    have hh' := Planar.placements_retain (Mid.partners idx) gs j (grid t) p[0] p[1] p[2]
    rw [pack_picks p] at hh'
    exact hh' hh
  apply Array.mem_flatMap.mpr
  refine ⟨i.val,mem_active hbit,?_⟩
  rw [Array.getElem?_eq_getElem i.isLt]
  exact Array.mem_map.mpr ⟨p,filterMiddle_mem hplace hm,rfl⟩

abbrev AtlasCovers := ∀ D : Finset (Tuple 3), packing cycleStep D → D.card = 33 →
  ∃ q : Fin atlasPlanes.size, ∃ g : Isometry 3, D = actOnCode g (atlasRepresentative q)

theorem full_projection (atlas : AtlasCovers) {C : Points} (hc : packing cycleStep C)
    {a : Axis} {t : Height} (ht : t ∈ fullStarts C a) :
    ∃ q : Fin atlasPlanes.size, ∃ w ∈ Bitsets.orbitImages atlasPlanes[q], TypeThree.RepresentsBand C a t w := by
  obtain ⟨hinj,hpack⟩ := Bands.band_projection hc a t
  have hcard := (Finset.card_image_of_injOn hinj).trans (Finset.mem_filter.mp ht).2
  obtain ⟨q,g,hg⟩ := atlas _ hpack hcard
  obtain ⟨w,hw,hrep⟩ := Bitsets.orbitImages_complete g atlasPlanes[q]
  exact ⟨q,w,hw,hrep.trans hg.symm⟩

theorem coversMiddle (atlas : AtlasCovers) {ss : Array Cube} (i : Fin ss.size)
    {C : Points} (hc : packing cycleStep C) {p : Placement} {t : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 ss[i]) (ht : TypeThree.RepresentsBand C 0 2 t)
    (hfull : ∀ c ∈ (Mid.contacts p).toArray, c.2 ∈ fullStarts C c.1.succ) :
    CoversMiddle C (Mid.index Bitsets.orbitImages atlasPlanes (Mid.allowed (ss.map grid))) ss[i] t p := by
  intro c hcm
  obtain ⟨q,w,hw,hrep⟩ := full_projection atlas hc (hfull c hcm)
  have follow (r : Cube) (u : Height) (h : TypeThree.RepresentsBand C 0 u r) :
      TypeThree.fastCut w 0 u = (grid r)[c.1][c.2] := by
    change TypeThree.fastCut w 0 u = (grid r)[c.1.val][c.2.val]
    simp only [grid, Vector.getElem_ofFn, TypeThree.fastCut_eq]
    exact (crosses_transverse c.1 h hrep).symm
  have hkey : Packed.key w = ((grid ss[i])[c.1][c.2],(grid t)[c.1][c.2]) :=
    Prod.ext (follow _ _ hs) (follow _ _ ht)
  have hall := Mid.allowed_mem (Array.mem_map_of_mem (f := grid) (Array.getElem_mem (xs := ss) i.isLt)) c.1 c.2
  have hfirst : (Packed.key w).1 ∈ Mid.allowed (ss.map grid) := hkey ▸ hall
  have hmem := Mid.within_index Bitsets.orbitImages atlasPlanes (Mid.allowed (ss.map grid))
    (Array.getElem_mem (xs := atlasPlanes) q.isLt) hw hfirst
  exact ⟨w,hrep,hkey ▸ hmem⟩

private theorem frame_gap {C : Points} {m : Frame} (hm : Marked m C) (hn : NoConsecutive C) (k : Axis) :
    m.gap k = 2 ∨ m.gap k = 3 := by
  have hm' := hm.1 k
  have hne : m.gap k ≠ 1 := by
    intro h
    exact hn k (m.base k) (hm.2.1 k false) (by simpa [start,h] using hm.2.1 k true)
  omega

def framePlacement (m : Frame) : Placement :=
  Vector.ofFn fun a => ⟨m.base a.succ, decide (m.gap a.succ = 3)⟩

theorem frame_full {m : Frame} {C : Points} (hm : Marked m C) (hn : NoConsecutive C)
    (c : Fin 3 × Fin 7) (h : c ∈ (Mid.contacts (framePlacement m)).toArray) :
    c.2 ∈ fullStarts C c.1.succ := by
  have starts (a : Fin 3) :
      (framePlacement m)[a].first ∈ fullStarts C a.succ ∧ (framePlacement m)[a].last ∈ fullStarts C a.succ := by
    change (framePlacement m)[a.val].first ∈ _ ∧ (framePlacement m)[a.val].last ∈ _
    simp only [framePlacement,Vector.getElem_ofFn,Planar.Pick.last]
    refine ⟨hm.2.1 a.succ false,?_⟩
    rcases frame_gap hm hn a.succ with hg | hg <;> simpa [start,hg] using hm.2.1 a.succ true
  simp only [Mid.contacts,List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact (starts _).1 | exact (starts _).2

theorem scan_retains (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33) (atlas : AtlasCovers)
    {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C)
    (hb : m.base 0 = 0) (hg : m.gap 0 = 2) (h113 : C.card = 113) (hn : NoConsecutive C)
    (ss ts : Array Cube) (i : Fin ss.size) {t r : Cube} (hr : r ∈ ts) (hw : t ∈ Bitsets.orbitImages r)
    (hs : TypeThree.RepresentsBand C 0 0 ss[i]) (ht : TypeThree.RepresentsBand C 0 2 t) :
    (⟨ss[i],t,framePlacement m⟩ : Layout) ∈ scan Bitsets.orbitImages atlasPlanes ss ts := by
  let p := framePlacement m
  let idx := Mid.index Bitsets.orbitImages atlasPlanes (Mid.allowed (ss.map grid))
  have H : CoversMiddle C idx ss[i] t p := coversMiddle atlas i hc hs ht (frame_full hm hn)
  apply Array.mem_flatMap.mpr
  refine ⟨r,hr,Array.mem_flatMap.mpr ⟨t,hw,?_⟩⟩
  apply forTarget_retains i
  · intro a j hj
    obtain ⟨w,_,hw'⟩ := H (a,j) (contact_mem p a j hj)
    exact partners_mem hw'
  · exact fun _ _ => reject_false h3 hc hm hb hg h113 hn hs ht H

/-- A successful evaluation excludes a normalized code with first support in
the source chunk and opposite support in a labelled orbit of the target chunk. -/
theorem check_sound (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33) (atlas : AtlasCovers)
    {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C)
    (hb : m.base 0 = 0) (hg : m.gap 0 = 2) (h113 : C.card = 113) (hn : NoConsecutive C)
    (ss ts : Array Cube) (i : Fin ss.size) {t r : Cube} (hr : r ∈ ts) (hw : t ∈ Bitsets.orbitImages r)
    (hs : TypeThree.RepresentsBand C 0 0 ss[i]) (ht : TypeThree.RepresentsBand C 0 2 t)
    (hcheck : check atlasPlanes ss ts) : False := by
  let p := framePlacement m
  let data := layoutCheck ⟨ss[i],t,p⟩
  have hscan := scan_retains h3 atlas hc hm hb hg h113 hn ss ts i hr hw hs ht
  have hl := Array.mem_map_of_mem (f := layoutCheck) hscan
  apply checked_full_batch atlas _ data hl hcheck hm hb hg hs ht _ hc
  intro j
  have hread : data.contacts[j] = (⟨((Mid.contacts p)[j]).1,((Mid.contacts p)[j]).2⟩ : Contact) :=
    Vector.getElem_map (xs := Mid.contacts p) (i := j.val) ..
  rw [hread]
  exact frame_full hm hn _ (Array.getElem_mem (xs := (Mid.contacts p).toArray) (i := j.val) (by simp))

end SevenCycle.TypeTwo.Search
