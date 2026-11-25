import SevenCycle.TypeTwo.Fast
import SevenCycle.TypeTwo.Normalize
import SevenCycle.Proof.Profiles

namespace SevenCycle.TypeTwo.Search
open Proof Blueprint Blueprint.SearchSpec

private theorem target_chunk (q : Fin atlasPlanes.size) :
    ∃ id : Fin 64, id.val * 16 ≤ q.val ∧ q.val < (id.val + 1) * 16 := by
  have size : atlasPlanes.size = 1016 := by decide +kernel
  have h : q.val < 1016 := lt_of_lt_of_le q.isLt size.le
  exact ⟨⟨q.val / 16, by omega⟩, by dsimp; omega, by dsimp; omega⟩

/-- Proposition 15 follows from the exhaustive checks over the opposite
support's atlas class. Every shard uses all 1,016 possible first supports. -/
theorem exclude_two_of_chunks
    (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33) (atlas : AtlasCovers)
    (hcheck : ∀ id : Fin 64, chunk id.val = true) (C : Points) (hc : packing cycleStep C)
    (h113 : C.card = 113) (p : Multiset ℕ) (hp : HasProfile C p) (h1 : 1 ∉ p) : 2 ∉ p := by
  intro h2
  obtain ⟨m, hm, hgap, rfl⟩ := Profiles.marked_frame h3 hc h113 hp
  obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp h2
  have hn : NoConsecutive C := Profiles.no_consecutive hm.1 hgap
    (fun j hj => h1 (Multiset.mem_map.mpr ⟨j, Finset.mem_univ j, hj⟩))
  obtain ⟨D,n,hD,hnM,b0,g2,d113,dnc,r,hs⟩ := normalize_two atlas hc hm h113 hn k hk
  have hf : 2 ∈ fullStarts D 0 := by simpa [start,b0,g2] using hnM.2.1 0 true
  obtain ⟨q,t,ht,hrep⟩ := full_projection atlas hD hf
  obtain ⟨id,hlo,hhi⟩ := target_chunk q
  exact chunk_sound h3 atlas hD hnM b0 g2 d113 dnc r q ht hs hrep id.val hlo hhi (hcheck id)

end SevenCycle.TypeTwo.Search
