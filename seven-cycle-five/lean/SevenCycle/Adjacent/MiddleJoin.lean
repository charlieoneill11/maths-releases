import SevenCycleRuntime.Middle
import SevenCycle.Adjacent.MiddleWindow
import SevenCycle.Adjacent.Support

namespace SevenCycle.Adjacent.Middle

open Proof Blueprint Bitsets

private theorem complete_sound (next : Nat → Bool) (n remaining tag acc want : Nat)
    (hw : want < 2^n) (allowed : ∀ i, want.testBit i = true → remaining.testBit i = true)
    (ok : complete next n remaining tag acc = true) : next (acc + tag*want) = true := by
  induction n generalizing remaining tag acc want with
  | zero =>
    have hz : want = 0 := by simpa using hw
    simpa [complete, hz] using ok
  | succ n ih =>
    by_cases hr : remaining = 0
    · have hz : want = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        cases h : want.testBit i
        · simp
        · simpa [hr] using allowed i h
      simpa [complete, hr, hz] using ok
    · simp only [complete, if_neg hr, Bool.and_eq_true] at ok
      have bound : want/2 < 2^n := by rw [pow_succ] at hw; omega
      have avail (i : Nat) (h : (want/2).testBit i = true) : (remaining/2).testBit i = true := by
        rw [Nat.testBit_div_two] at h ⊢
        exact allowed _ h
      cases hp : want.testBit 0 with
      | false =>
        have he := ih (remaining/2) (2*tag) acc (want/2) bound avail ok.1
        have split : 2*(want/2) = want := by have := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hp; omega
        rwa [Nat.mul_comm 2 tag, Nat.mul_assoc, split] at he
      | true =>
        have remain := allowed 0 hp
        have he := ih (remaining/2) (2*tag) (acc+tag) (want/2) bound avail
          (by simpa [remain] using ok.2)
        have split : 1+2*(want/2) = want := by have := Nat.mod_two_eq_one_iff_testBit_zero.mpr hp; omega
        rw [← split, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, ← Nat.mul_assoc, Nat.mul_comm tag 2]
        exact he

/-- Soundness of the array traversal. List induction here describes the
mathematics of Array.foldr; only the array iterator is compiled. -/
theorem walkRows_sound (common bits : Nat) (sub : bits &&& common = bits)
    (last : Nat → Nat → Bool) (wins : Array Choices)
    (hits : ∀ w ∈ wins, bits &&& w.scope ∈ w.picks) (fixed : Nat)
    (ok : walkRows common last wins fixed (bits &&& fixed) = true) :
    let f := wins.foldl (fun mask w => mask ||| w.scope) fixed
    last f (bits &&& f) = true := by
  have aux (xs : List Choices) (initial : Nat)
      (hw : ∀ w ∈ xs, bits &&& w.scope ∈ w.picks)
      (ho : xs.foldr (checkRow common) last initial (bits &&& initial) = true) :
      let f := xs.foldl (fun mask w => mask ||| w.scope) initial
      last f (bits &&& f) = true := by
    induction xs generalizing initial with
    | nil => exact ho
    | cons w ws ih =>
      have e := Array.all_eq_true'.mp ho _ (hw w (.head _))
      have exchange (a b c : Nat) : a &&& b &&& c = a &&& c &&& b := by
        rw [Nat.and_assoc, Nat.and_comm b c, ← Nat.and_assoc]
      have contained : (bits &&& w.scope) &&& common = bits &&& w.scope := by rw [exchange,sub]
      have agree : mergeable initial (bits &&& initial) w.scope (bits &&& w.scope) = true := by
        simp [mergeable,exchange]
      have combine : (bits &&& initial) ||| (bits &&& w.scope) = bits &&& (initial ||| w.scope) := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp [Nat.testBit_and,Nat.testBit_or,Bool.and_or_distrib_left]
      simp [contained,agree,combine] at e
      exact ih _ (fun r hr => hw r (.tail _ hr)) e
  rw [walkRows, ← Array.foldr_toList] at ok
  rw [← Array.foldl_toList]
  exact aux _ _ (fun w h => hits w (Array.mem_toList_iff.mp h)) ok

/-- The six contacts fix consistent exact restrictions of one bit vector.
Every compatible target using only common sites is submitted to the caller. -/
theorem join_sound (common bits n : Nat) (hs : bits &&& common = bits) (hn : bits < 2^n)
    (next : Nat → Bool) (wins : Array Choices)
    (hits : ∀ w ∈ wins, bits &&& w.scope ∈ w.picks) (fixed : Nat)
    (ok : join common n next wins fixed (bits &&& fixed) = true) : next bits = true := by
  have sub (i : Nat) (h : bits.testBit i = true) : common.testBit i = true := by
    have hbit := congrArg (fun a : Nat => a.testBit i) hs
    simpa [Nat.testBit_and, h] using hbit
  let finalScope := wins.foldl (fun mask w => mask ||| w.scope) fixed
  have done_ := walkRows_sound common bits hs
    (fun f sel => complete (fun extra => next (sel ||| extra)) n (common ^^^ (common &&& f)) 1 0)
    wins hits fixed ok
  let want := bits ^^^ (bits &&& finalScope)
  have want_bound : want < 2^n := Nat.lt_pow_two_of_testBit _ fun i hi => by
    have hb := Nat.testBit_lt_two_pow (hn.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hi))
    simp [want, Nat.testBit_xor, Nat.testBit_and, hb]
  have allowed (i : Nat) (h : want.testBit i = true) :
      (common ^^^ (common &&& finalScope)).testBit i = true := by
    simp only [want, Nat.testBit_xor, Nat.testBit_and] at h ⊢
    cases hb : bits.testBit i <;> cases hf : finalScope.testBit i <;>
      simp_all [show bits.testBit i = true → common.testBit i = true from sub i]
  have eq : (bits &&& finalScope) ||| want = bits := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [want, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and]
    cases bits.testBit i <;> cases finalScope.testBit i <;> rfl
  simpa only [Nat.one_mul, Nat.zero_add, eq] using
    complete_sound (fun extra => next ((bits &&& finalScope) ||| extra)) n _ 1 0 want
      want_bound allowed done_

end SevenCycle.Adjacent.Middle
