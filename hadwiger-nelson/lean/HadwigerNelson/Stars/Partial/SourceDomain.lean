import HadwigerNelson.Stars.Partial.Layout

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (physicalSource actualLabel)

/-- Every tested source is in the native tile and in the classifier window. -/
theorem source_domain (L : Layout.Physical) (i : Fin 136743) {z : Plane}
    (hz : z ∈ physicalSource (source i.val)) :
    Wave.colour PartialWave.datum z = some (actualLabel 1) ∧
    (0 ≤ z 0 ∧ z 0 ≤ 1) ∧
    BoxCheck.InBox (source i.val).box (10^12*z 0) (10^12*z 1) := by
  have tile := (L.subset i hz).1
  have x := (Placement.tile_coord_bounds _ tile).1
  refine ⟨Placement.colour_on_tile _ _ tile,⟨x.1.le,x.2.le⟩,?_⟩
  simpa only [CompleteWave.scale,Nat.cast_pow,Nat.cast_ofNat] using BoxCheck.source_in_box hz

theorem harmonic_alternate (L : Layout.Physical) (i : Fin 132621) :
    (source i.val).other = 6 ∨ (source i.val).other = 4 ∨ (source i.val).other = 2 := by
  have eq := L.other ⟨i.val,by omega⟩
  change (source i.val).other = Layout.alternate (Layout.family i.val) at eq
  rw [eq]
  have h := i.isLt
  simp only [Layout.family,if_pos h]
  split
  · exact Or.inl rfl
  split
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem native_alternate (L : Layout.Physical) (j : Fin 4122) :
    (source (132621+j.val)).other = 0 := by
  have eq := L.other ⟨132621+j.val,by omega⟩
  change (source (132621+j.val)).other = Layout.alternate (Layout.family _) at eq
  rw [eq]
  simp [Layout.family,Layout.alternate,show ¬132621+j.val<124995 by omega,
    show ¬132621+j.val<128531 by omega]

end HadwigerNelson.Stars.PartialCheck
