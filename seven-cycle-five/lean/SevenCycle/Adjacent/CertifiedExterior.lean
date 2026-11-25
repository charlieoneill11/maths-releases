import SevenCycle.Native.Exterior.Block0
import SevenCycle.Native.Exterior.Block1
import SevenCycle.Native.Exterior.Block2
import SevenCycle.Native.Exterior.Block3

import SevenCycle.Adjacent.FrameTransport

namespace SevenCycle.Adjacent.UnionTable

open Proof Blueprint Blueprint.SearchSpec



/-- A certified union in the centred frame extends to at most 112 words.
Enumeration of which unions occur is a separate hypothesis at its use site. -/
private theorem covered_bound (rows : Array String) (n : rows.size = 1776)
    (h0 : windowCheck rows (0, 444) = true)
    (h1 : windowCheck rows (444, 888) = true)
    (h2 : windowCheck rows (888, 1332) = true)
    (h3 : windowCheck rows (1332, 1776) = true) (s : String) (hs : s ∈ rows)
    (m : Frame) (hb : m.base = fun _ => 6) (hg : ∀ k, m.gap k = 1) (E : Points)
    (he : SearchSpec.Exterior m (rowSet (decode s).inside) E) :
    (rowSet (decode s).inside ∪ E).card ≤ 112 := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hs
  have top : i < 1776 := lt_of_lt_of_le hi n.le
  by_cases hlt0 : i < 444
  · exact windowCheck_sound _ _ h0 ⟨i,hi⟩ (by change 0 ≤ i; omega) (by change i < 444; omega) m hb hg E he
  by_cases hlt1 : i < 888
  · exact windowCheck_sound _ _ h1 ⟨i,hi⟩ (by change 444 ≤ i; omega) (by change i < 888; omega) m hb hg E he
  by_cases hlt2 : i < 1332
  · exact windowCheck_sound _ _ h2 ⟨i,hi⟩ (by change 888 ≤ i; omega) (by change i < 1332; omega) m hb hg E he
  exact windowCheck_sound _ _ h3 ⟨i,hi⟩ (by change 1332 ≤ i; omega) (by change i < 1776; omega) m hb hg E he

theorem table_bound (s : String) (hs : s ∈ UnionData.rows)
    (m : Frame) (hb : m.base = fun _ => 6) (hg : ∀ k, m.gap k = 1) (E : Points)
    (he : SearchSpec.Exterior m (rowSet (decode s).inside) E) :
    (rowSet (decode s).inside ∪ E).card ≤ 112 :=  covered_bound _ UnionData.size_rows Native.exterior_block0
  Native.exterior_block1 Native.exterior_block2 Native.exterior_block3 s hs m hb hg E he

/-- Transfer a verified table bound back to the original frame. -/
theorem exterior_of_image {m : Frame} (hg : ∀ k, m.gap k = 1) {D E : Points}
    (he : SearchSpec.Exterior m D E) {g : Isometry 4} (hc : centresAtZero m g)
    {s : String} (hs : s ∈ UnionData.rows) (hD : actOnCode g D = rowSet (decode s).inside) :
    (D ∪ E).card ≤ 112 := by
  obtain ⟨ext, card⟩ := exterior_centred hg hc he
  rw [← card, hD] at ⊢
  exact table_bound s hs centred rfl (fun _ => rfl) _ (hD ▸ ext)

end SevenCycle.Adjacent.UnionTable
