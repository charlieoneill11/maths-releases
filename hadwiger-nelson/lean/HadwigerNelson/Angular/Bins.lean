import HadwigerNelson.Angular.Segments
import HadwigerNelson.Data.CompleteWave

namespace HadwigerNelson.Angular
open Arithmetic

theorem Segments.area_eq_zero_of_misses (tree : Segments) (ok : tree.Valid)
    {d lo d' lo' : Int} (h : tree.misses d lo) (hd : d ≤ d') (hl : lo ≤ lo') :
    tree.area d' lo' = 0 := by
  induction tree with
  | single s =>
    change decide (s.stop ≤ lo ∨ max s.left s.right ≤ d) = true at h
    rcases of_decide_eq_true h with hy|hx
    · exact if_pos (Or.inl (hy.trans hl))
    · exact if_pos (Or.inr (hx.trans hd))
  | branch t a b ia ib =>
    simp only [misses, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with hz|⟨ha,hb⟩
    · exact area_zero _ ok _ _ (hz.imp (·.trans hl) (·.trans hd))
    · simp only [Segments.area, ia ok.2.1 ha, ib ok.2.2 hb, Int.add_zero]


end HadwigerNelson.Angular
