import SevenCycle.Adjacent.Contacts

namespace SevenCycle.Adjacent.Contacts

open Proof Blueprint Bitsets

private theorem middle_eq (w : Cube) : middle w = Bitsets.lev w 0 1 := by
  change clean (w.get 1) = Bitsets.lev w 0 1
  apply plane_eq_of_set_eq (canonical_clean _) (canonical_lev w 0 1)
  have coords : ∀ x : Tuple 2, (0 : Fin 3).insertNth (α := fun _ => ZMod 7) (1 : ZMod 7) x = ![1,x 0,x 1] := by decide
  ext x
  simp only [mem_planeSet, planeMem_clean, Bitsets.lev, planeMem_buildPlane, coords]
  rfl

private theorem mem_level {n : ℕ} {C : Finset (Tuple (n+1))} {a : Fin (n+1)} {j : ZMod 7} {x : Tuple n} :
    x ∈ projectedLevel C a j ↔ ∃ y ∈ C, y a = j ∧ dropCoord a y = x := by
  simp [projectedLevel, level, and_assoc]

private theorem mem_band {n : ℕ} {C : Finset (Tuple (n+1))} {a : Fin (n+1)} {j : ZMod 7} {x : Tuple n} :
    x ∈ projectedBand C a j ↔ ∃ y ∈ C, (y a = j ∨ y a = j+1) ∧ dropCoord a y = x := by
  simp [projectedBand, band, and_assoc]

/-- Cutting the physical middle layer at a transverse window yields the
middle height in that window's atlas image. -/
theorem middle_window {C : SearchSpec.Points} {u w : Cube}
    (hu : cubeSet u = projectedLevel C 0 1) (a : Fin 3) (j : Height)
    (hw : TypeThree.RepresentsBand C a.succ j w) :
    TypeThree.fastCut u a j = middle w := by
  rw [TypeThree.fastCut_eq, middle_eq]
  apply plane_eq_of_set_eq (canonical_cut u a j) (canonical_lev w 0 1)
  rw [planeSet_cut, planeSet_lev]
  change projectedBand (cubeSet u) a j = projectedLevel (cubeSet w) 0 1
  rw [hu, hw]
  have ht : ∀ a : Fin 3, a.succ.succAbove 0 = 0 := by decide
  have eq : ∀ (a : Fin 3) (i : Fin 2),
      (0 : Fin 4).succAbove (a.succAbove i) = a.succ.succAbove ((0 : Fin 3).succAbove i) := by decide
  ext x
  constructor
  · intro h
    obtain ⟨_, hl, hb, rfl⟩ := mem_band.mp h
    obtain ⟨y, hC, hy, rfl⟩ := mem_level.mp hl
    refine mem_level.mpr ⟨_, mem_band.mpr ⟨y, hC, ?_, rfl⟩, ?_, ?_⟩
    · simpa [dropCoord] using hb
    · simpa [dropCoord, ht] using hy
    · funext i; exact congrArg y (eq a i).symm
  · intro h
    obtain ⟨_, hb, hl, rfl⟩ := mem_level.mp h
    obtain ⟨y, hC, hy, rfl⟩ := mem_band.mp hb
    refine mem_band.mpr ⟨_, mem_level.mpr ⟨y, hC, ?_, rfl⟩, ?_, ?_⟩
    · simpa [dropCoord, ht] using hl
    · simpa [dropCoord] using hy
    · funext i; exact congrArg y (eq a i)

theorem middle_entry (atlas : AtlasComplete) {C : SearchSpec.Points} (hc : packing cycleStep C)
    {s t u : Cube} (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1) {a : Fin 3} {j : Height} (hf : j ∈ fullStarts C a.succ) :
    TypeThree.fastCut u a j ∈ (index orbitImages atlasPlanes).getD (anchorKey s t a j) #[] := by
  obtain ⟨w, hw, h⟩ := contact_covers atlas hc hs ht hf
  rw [middle_window hu a j hw]
  exact h

end SevenCycle.Adjacent.Contacts
