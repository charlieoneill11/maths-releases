import LeastPrime.Checker.Grid
import LeastPrime.Checker.CertificateData

/-! The symmetric grid windows used in the numerical bounds. -/

namespace LeastPrime.Checker

open Set

theorem denote_symmetricWindow {a b : ℕ} (hab : a ≤ b) (hb : b ≤ unit) :
    denote (symmetricWindow a b) =
      Icc (grid a) (grid b) ∪ Icc (1 - grid b) (1 - grid a) := by
  simp only [symmetricWindow, denote, interval, union_empty,
    grid_sub hb, grid_sub (hab.trans hb), grid_unit]

theorem valid_symmetricWindow {a b : ℕ} (hab : a ≤ b) (hsep : b < unit - b) :
    Valid (symmetricWindow a b) := by
  have hb : b ≤ unit := by omega
  have hI : Good (a, b) := ⟨hab, hb⟩
  refine ⟨?_, ?_, ?_⟩
  · intro I hI'
    simp only [symmetricWindow, List.mem_cons, List.not_mem_nil, or_false] at hI'
    rcases hI' with rfl | rfl
    · exact hI
    · exact good_reflect hI
  · simp [Segregated, symmetricWindow, hsep]
  · have heq : denote (symmetricWindow a b) =
        interval (a, b) ∪ interval (reflectInterval (a, b)) := by
      simp [symmetricWindow, denote, reflectInterval]
    rw [IsSymmetric, heq]
    change _ = (fun t : ℝ => 1 - t) '' (_ ∪ _)
    rw [Set.image_union]
    change _ = reflect (interval (a, b)) ∪ reflect (interval (reflectInterval (a, b)))
    rw [← interval_reflect hI, ← interval_reflect (good_reflect hI),
      reflectInterval_reflectInterval hI, union_comm]

theorem denote_symmetricWindow_tin : denote (symmetricWindow 142858 199999) = Tin := by
  rw [denote_symmetricWindow (by decide) (by decide), Tin]
  norm_num [grid, unit]

theorem denote_symmetricWindow_tout : denote (symmetricWindow 142857 200000) = Tout := by
  rw [denote_symmetricWindow (by decide) (by decide), Tout]
  norm_num [grid, unit]

end LeastPrime.Checker
