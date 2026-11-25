import HadwigerNelson.Stars.PhysicalSource

/-! Geometric conclusions of the source layout check for the complete wave. -/

namespace HadwigerNelson.Stars.BoxCheck

/-- The two box families are contained in the lower half-tile. Each family has disjoint
interiors. When both families are used, harmonic boxes are kept only if their
`separate` flag certifies disjointness from every saturated box. -/
structure PhysicalLayout : Prop where
  harmonic_subset (i : Fin 14464) :
    physicalSource (source i.val) ⊆ Wave.halfTile Wave.completeDatum false
  saturated_subset (i : Fin 252) :
    physicalSource (saturated i.val) ⊆ Wave.halfTile Wave.completeDatum false
  harmonic_disjoint {i j : Fin 14464} (hij : i ≠ j) :
    Disjoint (physicalSource (source i.val)) (physicalSource (source j.val))
  saturated_disjoint {i j : Fin 252} (hij : i ≠ j) :
    Disjoint (physicalSource (saturated i.val)) (physicalSource (saturated j.val))
  mixed_disjoint (i : Fin 14464) (j : Fin 252) (keep : (source i.val).separate = true) :
    Disjoint (physicalSource (source i.val)) (physicalSource (saturated j.val))

theorem checkSourceBoxes_physical (pass : checkSourceBoxes = true) : PhysicalLayout := by
  have valid := checkSourceBoxes_spec pass
  refine ⟨fun i ↦ physical_source_half i (valid.1 i),
    fun i ↦ physical_saturated_half i (valid.2 i), ?_, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun _ hi hj ↦
      checked_disjoint (valid.1 i) (valid.1 j) (Fin.val_ne_of_ne hij) hi hj
  · intro i j hij
    exact Set.disjoint_left.mpr fun _ hi hj ↦ saturated_disjoint i j hij hi hj
  · intro i j keep
    exact Set.disjoint_left.mpr fun _ hi hj ↦ harmonic_separate_saturated keep j hi hj

end HadwigerNelson.Stars.BoxCheck
