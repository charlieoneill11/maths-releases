import ZetaSixth.ExponentProofs.BandIII
import ZetaSixth.ExponentProofs.SmallBands

namespace ZetaSixth.Exponents

/-- The ranges of Lemma 90 exhaust the mark region. In the shared band, the two
affine caps change order at ς = 4/35. -/
theorem markRegion_bands (q : Degrees) (h : q.InMarkRegion) :
    q.BandI ∨ q.BandII ∨ q.BandIII := by
  obtain ⟨_, hs₃, _, hMark⟩ := h
  by_cases hs₁₀ : q.ς < 1 / 10
  · exact Or.inl hs₁₀
  right
  have h₁₀ : 1 / 10 ≤ q.ς := le_of_not_gt hs₁₀
  by_cases hs₇ : q.ς < 1 / 7
  · simp only [Degrees.markCap, hs₁₀, hs₇, if_false, if_true] at hMark
    by_cases hCross : q.ς ≤ 4 / 35
    · have hCap : (2 - 7 * q.ς) / 4 ≤ (3 - 21 * q.ς) / 2 := by
        linarith only [markCapDifference q.ς, hCross]
      rw [max_eq_left hCap] at hMark
      exact Or.inl ⟨h₁₀, by linarith only [hCross], hMark⟩
    · have hCap : (3 - 21 * q.ς) / 2 ≤ (2 - 7 * q.ς) / 4 := by
        linarith only [markCapDifference q.ς, lt_of_not_ge hCross]
      rw [max_eq_right hCap] at hMark
      exact Or.inr (Or.inl ⟨h₁₀, hs₇, hMark⟩)
  right
  by_cases hs₄ : q.ς < 1 / 4
  · simp only [Degrees.markCap, hs₁₀, hs₇, hs₄, if_false, if_true] at hMark
    exact Or.inr (Or.inl ⟨le_of_not_gt hs₇, hs₄, hMark⟩)
  · simp only [Degrees.markCap, hs₁₀, hs₇, hs₄, if_false] at hMark
    exact Or.inr (Or.inr ⟨le_of_not_gt hs₄, hs₃, hMark⟩)

/-- Lemma 90, with its separate saving estimates on each of the three ranges. -/
theorem lemma90 : Lemma90 := by
  intro q hq hRegion
  exact ⟨bandI_saves q hq, bandII_saves q hq, bandIII_saves q hq hRegion.1⟩

/-- The covering conclusion of Lemma 90 for every tuple in the mark region. -/
theorem lemma90_covering : Covering := by
  intro q hq hRegion
  obtain ⟨h₁, h₂, h₃⟩ := lemma90 q hq hRegion
  rcases markRegion_bands q hRegion with hb | hb | hb
  · rcases h₁ hb with ht | hu | hs
    · exact Or.inl ht
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr (Or.inl hs))
  · rcases h₂ hb with ht | hu | hs | hd
    · exact Or.inl ht
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hd))))
  · rcases h₃ hb with ht | hu | hr | hd | hl
    · exact Or.inl ht
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))

end ZetaSixth.Exponents
