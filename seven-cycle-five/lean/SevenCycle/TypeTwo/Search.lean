import SevenCycle.TypeTwo.Check
import SevenCycleRuntime.TypeTwoSearch

/-! End-to-end type-two checker for chosen source and opposite support classes. -/

namespace SevenCycle.TypeTwo.Search

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry
open Bitsets (Cube)

def layoutCheck (l : Layout) : LayoutCheck :=
  ⟨l.left,l.right,(Mid.contacts l.marks).map (fun (a,t) => ⟨a,t⟩)⟩

/-- Source and opposite support class arrays can be chunked independently.
The catalog and final projection index always use every supplied atlas class. -/
def check (catalog sources targets : Array Cube) : Bool :=
  checkBatch catalog ((scan Bitsets.orbitImages catalog sources targets).map layoutCheck)

theorem mem_active {n i : Nat} (h : n.testBit i) : i ∈ active n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn : n ≠ 0 := by rintro rfl; simp at h
    rw [active, dif_neg hn]
    apply Array.mem_push.mpr
    by_cases hi : i = n.log2
    · exact Or.inr hi
    · have hlt : i < n.log2 := lt_of_le_of_ne ((Nat.le_log2 hn).mpr (Nat.ge_two_pow_of_testBit h)) hi
      exact Or.inl (ih _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.log2_self_le hn))
        (by simp [Nat.testBit_mod_two_pow,hlt,h]))

end SevenCycle.TypeTwo.Search
