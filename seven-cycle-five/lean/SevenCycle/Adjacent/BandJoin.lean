import SevenCycleRuntime.AdjacentBands
import SevenCycle.Adjacent.Support
import SevenCycle.Adjacent.Slabs
import SevenCycle.TypeThree.Coverage
import SevenCycle.TypeThree.FastCuts

namespace SevenCycle.Adjacent.BandJoin

open Bitsets Proof Blueprint

private def outer (r w : Cube) : Cube :=
  Vector.ofFn fun h : Fin 7 => if h.val < 3 then 0 else r.get h &&& w.get h

private theorem get_outer (r w : Cube) (h : Fin 7) :
    (outer r w).get h = if h.val < 3 then 0 else r.get h &&& w.get h := by
  simp [outer, Vector.get]

private theorem outer_set (r w : Cube) : cubeSet (outer r w) =
    (cubeSet r ∩ cubeSet w).filter (fun x => 3 ≤ (x 0).val) := by
  ext x
  simp only [mem_cubeSet, Finset.mem_filter, Finset.mem_inter, cubeMem, get_outer]
  split
  · rename_i h
    change (x 0).val < 3 at h
    simp [Nat.not_le_of_lt h]
  · rename_i h
    change ¬ (x 0).val < 3 at h
    simp [Nat.le_of_not_gt h, UInt64.toNat_and, Nat.testBit_and]

theorem exteriorCommon_eq (r w : Cube) : exteriorCommon r w =
    ((cubeSet r ∩ cubeSet w).filter (fun x => 3 ≤ (x 0).val)).card := by
  rw [← outer_set, ← cubeCard_eq]
  have zero : planeCard 0 = 0 := by decide
  have useCard (p : UInt64) : SevenCycleRuntime.Adjacent.maskCard p = planeCard p := maskCard_eq p
  change _ = planeCard 0 + planeCard 0 + planeCard 0 + planeCard (r.get 3 &&& w.get 3) +
    planeCard (r.get 4 &&& w.get 4) + planeCard (r.get 5 &&& w.get 5) + planeCard (r.get 6 &&& w.get 6)
  simp [exteriorCommon, useCard, zero]

private theorem distinct_axes : ∀ a b : Fin 3, a ≠ b →
    a.succ.succAbove (transverse a b) = b.succ ∧
    ∀ j : Fin 2, a.succ.succAbove ((transverse a b).succAbove j) =
      b.succ.succAbove ((transverse b a).succAbove j) := by decide

theorem crossing_of_bands {C : Finset (Tuple 4)} {s t : Port} (h : s.axis ≠ t.axis)
    {r w : Cube} (hr : TypeThree.RepresentsBand C s.axis.succ s.start r)
    (hw : TypeThree.RepresentsBand C t.axis.succ t.start w) :
    TypeThree.fastCut r (transverse s.axis t.axis) t.start =
      TypeThree.fastCut w (transverse t.axis s.axis) s.start := by
  rw [TypeThree.fastCut_eq, TypeThree.fastCut_eq]
  exact TypeThree.equal_cuts (distinct_axes _ _ h).1 (distinct_axes _ _ h.symm).1
    (distinct_axes _ _ h).2 hr hw

private theorem project_stripe {C : SearchSpec.Points} {l : Fin 4} {t : ZMod 7} {x : Tuple 4}
    (hx : x ∈ SearchSpec.stripe C l t) : dropCoord l x ∈ projectedBand C l t ∧ x l = 0 := by
  obtain ⟨y, hy, hyt, rfl⟩ := FrameGeometry.mem_face.mp hx
  exact ⟨Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy,hyt⟩,
    (FrameGeometry.drop_setHeight l y 0).symm⟩, by simp [SearchSpec.setHeight]⟩

/-- Compute the centre-capacity condition in the two transverse projections
after flattening their common omitted coordinate. -/
theorem projected_capacity (C D : SearchSpec.Points) (m : SearchSpec.Frame) (a : Fin 3)
    (base : m.base 0 = 0) (gap : m.gap 0 = 1)
    (cap : SearchSpec.CentreCapacity m 0 a.succ D (SearchSpec.projections m C)) :
    16 ≤ (D.filter (fun x => x a.succ = SearchSpec.start m a.succ true)).card +
      (((projectedBand C a.succ (SearchSpec.start m a.succ false)) ∩
        (projectedBand C a.succ (SearchSpec.start m a.succ true))).filter
          (fun x => 3 ≤ (x 0).val)).card := by
  let P := SearchSpec.projections m C
  let X := (P a.succ false ∩ P a.succ true).filter (fun x => ¬ SearchSpec.inSlab m 0 x)
  have left {x} (hx : x ∈ X) := (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
  have flat {x} (hx : x ∈ X) : x a.succ = 0 := (project_stripe (left hx)).2
  have inj : Set.InjOn (dropCoord a.succ) X := by
    intro x hx y hy eq
    funext j
    apply (Fin.forall_iff_succAbove a.succ).mpr _ j
    exact ⟨(flat hx).trans (flat hy).symm, fun t => congrFun eq t⟩
  have sub : X.image (dropCoord a.succ) ⊆
      (((projectedBand C a.succ (SearchSpec.start m a.succ false)) ∩
        (projectedBand C a.succ (SearchSpec.start m a.succ true))).filter
          (fun x => 3 ≤ (x 0).val)) := by
    rintro u hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hp, hout⟩ := Finset.mem_filter.mp hx
    have h0 : a.succ.succAbove 0 = 0 := (by decide : ∀ b : Fin 3, b.succ.succAbove 0 = 0) a
    have residues : ∀ t : ZMod 7, t ∉ ({0,1,2} : Finset (ZMod 7)) → 3 ≤ t.val := by decide
    refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨(project_stripe (left hx)).1,
      (project_stripe (Finset.mem_inter.mp hp).2).1⟩, ?_⟩
    rw [dropCoord, h0]
    apply residues
    simpa [SearchSpec.inSlab, SearchSpec.start, gap, base] using hout
  have hc := Finset.card_le_card sub
  rw [Finset.card_image_iff.mpr inj] at hc
  exact cap.trans (Nat.add_le_add_left hc _)

/-- If every domain contains its actual projected band, all different-axis
checks hold. On the same axis the only additional test is the centre bound:
the anchor slab's known words plus common words at anchor heights 3–6. -/
theorem join_retains (C : Finset (Tuple 4)) (ports : Ports) (domains : Domains)
    (covered : ∀ i : Fin 6, ∃ r ∈ domains.get i,
      TypeThree.RepresentsBand C (ports.get i).axis.succ (ports.get i).start r)
    (cap : ∀ i j : Fin 6, i ≠ j → (ports.get i).axis = (ports.get j).axis →
      (ports.get i).gap = 1 →
      16 ≤ (ports.get i).known +
        (((projectedBand C (ports.get i).axis.succ (ports.get i).start) ∩
          (projectedBand C (ports.get j).axis.succ (ports.get j).start)).filter
            (fun x => 3 ≤ (x 0).val)).card) : canJoin ports domains = true := by
  choose w mem rep using covered
  apply canJoin_of_selection ports domains w mem
  intro i j ne
  by_cases axes : (ports.get i).axis = (ports.get j).axis
  · simp only [pairOK, axes, ↓reduceIte, Bool.or_eq_true_iff, bne_iff_ne, decide_eq_true_eq]
    by_cases gap : (ports.get i).gap = 1
    · apply Or.inr
      rw [exteriorCommon_eq, rep i, rep j]
      exact cap i j ne axes gap
    · exact Or.inl gap
  · simp only [pairOK, axes, ↓reduceIte, beq_iff_eq]
    exact crossing_of_bands axes (rep i) (rep j)

def physicalPorts (m : SearchSpec.Frame) (known : Vector ℕ 3) : Ports :=
  portsFor (Vector.ofFn fun a => m.base a.succ) (Vector.ofFn fun a => m.gap a.succ) known

theorem port_get (m : SearchSpec.Frame) (known : Vector ℕ 3) (i : Fin 6) :
    (physicalPorts m known).get i =
      ⟨axisOf i, SearchSpec.start m (axisOf i).succ (later i),
        m.gap (axisOf i).succ, known.get (axisOf i)⟩ := by
  simp [physicalPorts, portsFor, SearchSpec.start, Vector.get]
  rfl

private theorem opposite : ∀ i j : Fin 6, i ≠ j → axisOf i = axisOf j →
    (later i = false ∧ later j = true) ∨ (later i = true ∧ later j = false) := by decide

/-- The six-band join accepts every normalized marked code once its domain
arrays contain the actual transverse bands. The supplied centre counts may
be upper bounds on the exact slab populations. -/
theorem actual_join (C : SearchSpec.Points) (m : SearchSpec.Frame) (hc : packing cycleStep C)
    (hm : SearchSpec.Marked m C) (base : m.base 0 = 0) (gap : m.gap 0 = 1)
    (known : Vector ℕ 3) (domains : Domains)
    (covered : ∀ i : Fin 6, ∃ r ∈ domains.get i, TypeThree.RepresentsBand C
      (axisOf i).succ (SearchSpec.start m (axisOf i).succ (later i)) r)
    (hcount : ∀ a : Fin 3, m.gap a.succ = 1 →
      ((SearchSpec.slab m 0 (SearchSpec.projections m C 0 false) (SearchSpec.projections m C 0 true)
        (SearchSpec.plane C 0 (SearchSpec.start m 0 true))).filter
        (fun x => x a.succ = SearchSpec.start m a.succ true)).card ≤ known.get a) :
    canJoin (physicalPorts m known) domains = true := by
  apply join_retains C
  · simpa only [port_get] using covered
  intro i j nij
  simp only [port_get]
  intro eq hg
  have cap := (Adjacent.six_bands hc hm gap).2.2 (axisOf i).succ (Fin.succ_ne_zero _) hg
  have bound := projected_capacity C _ m (axisOf i) base gap cap
  have bigger := bound.trans (Nat.add_le_add_right (hcount _ hg) _)
  rw [← eq]
  rcases opposite i j nij eq with ⟨hi,hj⟩ | ⟨hi,hj⟩
  · simpa only [hi,hj] using bigger
  · simpa only [hi,hj,Finset.inter_comm] using bigger

end SevenCycle.Adjacent.BandJoin
