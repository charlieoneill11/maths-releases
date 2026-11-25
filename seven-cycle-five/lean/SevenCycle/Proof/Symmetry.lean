import SevenCycle.Blueprint.Definitions

namespace SevenCycle.Proof.Symmetry

open Blueprint

/-- Undo each output translation and sign, in inverse-permuted order. -/
def undo {n : ℕ} (g : Isometry n) : Isometry n :=
  (g.1.symm, fun k => g.2.1 (g.1.symm k),
    fun k => if g.2.1 (g.1.symm k) then g.2.2 (g.1.symm k) else -g.2.2 (g.1.symm k))

theorem undo_act {n : ℕ} (g : Isometry n) (x : Tuple n) : act (undo g) (act g x) = x := by
  funext k
  simp only [act, undo, Equiv.apply_symm_apply]
  split <;> simp_all

theorem act_undo {n : ℕ} (g : Isometry n) (x : Tuple n) : act g (act (undo g) x) = x := by
  funext k
  simp only [act, undo, Equiv.symm_apply_apply]
  split <;> simp_all

private theorem step_iff : ∀ (sign : Bool) (t a b : ZMod 7),
    cycleStep ((if sign then -a else a) + t) ((if sign then -b else b) + t) ↔ cycleStep a b := by
  unfold cycleStep
  decide

private theorem preserve {n : ℕ} (g : Isometry n) {x y : Tuple n}
    (h : conflict cycleStep x y) : conflict cycleStep (act g x) (act g y) := by
  refine ⟨fun e => h.1 ?_, fun k => (step_iff _ _ _ _).2 (h.2 (g.1 k))⟩
  simpa only [undo_act] using congrArg (act (undo g)) e

theorem act_confusable {n : ℕ} (g : Isometry n) (x y : Tuple n) :
    conflict cycleStep (act g x) (act g y) ↔ conflict cycleStep x y := by
  exact ⟨fun h => by simpa only [undo_act] using preserve (undo g) h, preserve g⟩

theorem isometry_orders :
    Fintype.card (Isometry 2) = 392 ∧ Fintype.card (Isometry 3) = 16464 := by
  simp [Isometry, Tuple, Fintype.card_perm, Nat.factorial]

end SevenCycle.Proof.Symmetry
