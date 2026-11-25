import Chowla.CheckerRows
import Chowla.CheckerMatchingProofs
import Chowla.Model.MatchingSum

namespace Chowla.Checker

open Set

theorem eraseEach_members {widths : List ℚ} {choice : ℚ × List ℚ}
    (h : choice ∈ eraseEach widths) : choice.1 ∈ widths ∧ (∀ a ∈ choice.2, a ∈ widths) := by
  induction widths generalizing choice with
  | nil => simp [eraseEach] at h
  | cons a widths ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨by simp, fun b hb => by simp [hb]⟩
    · obtain ⟨⟨b, rest⟩, hb, rfl⟩ := List.mem_map.mp h
      obtain ⟨hm, hr⟩ := ih hb
      refine ⟨by simp [hm], ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp
      · simp [hr c hc]

theorem rectangleTail_cast (A : List ℚ) (ha : ∀ a ∈ A, (0 : ℚ) < a) :
    (rectangleTail A : ℝ) = Chowla.rectangleTail (A.map (fun a : ℚ => (a : ℝ))) := by
  by_cases h : 2 ≤ A.length
  · simpa only [Chowla.rectangleTail, List.length_map, if_pos h, List.map_map,
      Function.comp_def] using rectangleTail_sound A ha h
  · have hn : A.length < 2 := Nat.lt_of_not_ge h
    simp [rectangleTail, Chowla.rectangleTail, hn, h]

/-- Exact arithmetic interpretation of the marked cumulant and the two possible
terms from an exceptional unmarked block, before reindexing labelled matchings. -/
theorem contractionTerm_sound (p : Spline) (widths : List ℚ) (hp : IsProfile p.toReal)
    (hsorted : widths.Pairwise (· ≤ ·)) (hwidths : ∀ a ∈ widths, (a : ℝ) ∈ Ioc 0 1) :
    let A := widths.map fun a : ℚ => (a : ℝ)
    (contractionTerm (splinePrimitives p) widths : ℝ) =
      cumulant (p.toReal :: A.map rectangle) +
        Chowla.rectangleTail A * cumulant [p.toReal] +
        ((eraseEach widths).map fun (a, rest) =>
          Chowla.rectangleTail (rest.map (fun b : ℚ => (b : ℝ))) *
            cumulant [p.toReal, rectangle (a : ℝ)]).sum := by
  have hq : ∀ a ∈ widths, (0 : ℚ) < a := by
    intro a ha
    exact_mod_cast (hwidths a ha).1
  have hn : ∀ a ∈ widths, (0 : ℚ) ≤ a := fun a ha => (hq a ha).le
  rw [contractionTerm_expansion (splinePrimitives p) widths hsorted hn]
  simp only [Rat.cast_add, Rat.cast_mul, markedCumulant_sound p widths hp hwidths,
    mean_cumulant_sound p hp, rectangleTail_cast widths hq, List.map_map, Function.comp_def]
  congr 1
  rw [cast_width_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro choice hc
  obtain ⟨ha, hrest⟩ := eraseEach_members hc
  rcases choice with ⟨a, rest⟩
  change (↑(rectangleTail rest * covariance (splinePrimitives p) a) : ℝ) = _
  rw [Rat.cast_mul, rectangleTail_cast rest (fun b hb => hq b (hrest b hb)),
    covariance_cumulant_sound p hp a (hwidths a ha)]

end Chowla.Checker
