import SevenCycle.Proof.Deficits

namespace SevenCycle.Proof.Profiles

open Blueprint Blueprint.SearchSpec

private theorem orient : ∀ i j : Height,
    i + (cycleDistance i j : Height) = j ∨ j + (cycleDistance i j : Height) = i := by
  unfold cycleDistance
  decide

private theorem unit_distance : ∀ i : Height, i ≠ i+1 ∧ cycleDistance i (i+1) = 1 := by
  unfold cycleDistance
  decide

private theorem choose_starts (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33)
    {C : Points} (hc : packing cycleStep C) (h113 : C.card = 113) (k : Axis) (d : ℕ)
    (hd : AxisGap C k d) :
    ∃ a, a ∈ fullStarts C k ∧ a + (d : Height) ∈ fullStarts C k ∧
      (d = 1 → HasCentre C k (a + (d : Height))) := by
  obtain ⟨i, hi, j, hj, _, hij⟩ := hd.1
  have pair : ∃ a ∈ fullStarts C k, a + (d : Height) ∈ fullStarts C k := by
    have hor := orient i j
    rw [hij] at hor
    rcases hor with he | he
    · exact ⟨i, hi, he.symm ▸ hj⟩
    · exact ⟨j, hj, he.symm ▸ hi⟩
  by_cases e : d = 1
  · rw [e] at pair ⊢
    obtain ⟨c, hc'⟩ := Deficits.deficits_two h3 C hc h113 k (by simpa using pair)
    exact ⟨c-1, hc'.1, by simpa using hc'.2.1, fun _ => by simpa using hc'⟩
  · obtain ⟨a, ha, he⟩ := pair
    exact ⟨a, ha, he, fun h => (e h).elim⟩

/-- Realise the least distances simultaneously. Adjacent pairs have the centres chosen in Lemma 4. -/
theorem marked_frame (h3 : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card ≤ 33)
    {C : Points} (hc : packing cycleStep C) (h113 : C.card = 113)
    {p : Multiset ℕ} (hp : HasProfile C p) :
    ∃ m : Frame, Marked m C ∧ (∀ k, AxisGap C k (m.gap k)) ∧
      p = (Finset.univ : Finset Axis).val.map m.gap := by
  obtain ⟨d, hd, rfl⟩ := hp
  choose base hb hs hcentre using fun k => choose_starts h3 hc h113 k _ (hd k)
  let m : Frame := ⟨fun k => (d k).val + 1, base⟩
  refine ⟨m, ⟨?_, ?_, ?_⟩, hd, rfl⟩
  · intro k
    have := (d k).isLt
    change 1 ≤ (d k).val + 1 ∧ (d k).val + 1 ≤ 3
    omega
  · intro k b
    cases b
    · exact hb k
    · exact hs k
  · exact hcentre

theorem gap_mem (m : Frame) (k : Axis) : m.gap k ∈ (Finset.univ : Finset Axis).val.map m.gap :=
  Multiset.mem_map.mpr ⟨k, Finset.mem_univ k, rfl⟩

theorem no_consecutive {C : Points} {m : Frame} (hm : ValidFrame m)
    (hgap : ∀ k, AxisGap C k (m.gap k)) (hn : ∀ k, m.gap k ≠ 1) : NoConsecutive C := by
  intro k t ht ht'
  have hd := (hgap k).2 t ht (t+1) ht' (unit_distance t).1
  rw [(unit_distance t).2] at hd
  exact hn k (Nat.le_antisymm hd (hm k).1)

end SevenCycle.Proof.Profiles
