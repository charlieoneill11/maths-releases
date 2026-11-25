import HadwigerNelson.Data.CompleteWave

namespace HadwigerNelson.CompleteWave

private def tableTest (i : Nat) : Bool := decide (
  4*scale < 5*ordinate i ∧ ordinate i < scale ∧
  ordinate (2048-i) = ordinate i ∧
  (i ≤ 1024 → ordinate i + ordinate (i+1024) = 2*xInt))

def ValidProfile : Prop := (Array.range 2049).all tableTest = true

theorem ordinate_facts (checked_facts : ValidProfile) {i : Nat} (hi : i ≤ 2048) :
    4*scale < 5*ordinate i ∧ ordinate i < scale ∧ ordinate (2048-i) = ordinate i ∧
    (i ≤ 1024 → ordinate i + ordinate (i+1024) = 2*xInt) := by
  have h := Array.all_eq_true_iff_forall_mem.mp checked_facts i
    (Array.mem_range.mpr (by omega : i < 2049))
  exact of_decide_eq_true h

/-- Check a bounded block of fixed integer ordinates. -/
def checkBlock (k : Nat) : Bool := (Array.range 32).all fun j =>
  if 32*k+j < 2049 then tableTest (32*k+j) else true

theorem validProfile_of_blocks (checked : ∀ k : Fin 65, checkBlock k.val = true) : ValidProfile := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro i hi
  have ilt := Array.mem_range.mp hi
  let k : Fin 65 := ⟨i/32,by omega⟩
  have h := Array.all_eq_true_iff_forall_mem.mp (checked k) (i%32)
    (Array.mem_range.mpr (Nat.mod_lt _ (by decide : 0 < 32)))
  have eq : 32*k.val+i%32 = i := by dsimp [k]; omega
  simpa [eq,ilt] using h

end HadwigerNelson.CompleteWave
