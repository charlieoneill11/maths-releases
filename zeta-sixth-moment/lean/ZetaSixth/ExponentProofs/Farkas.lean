import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace ZetaSixth.Exponents.Farkas

open scoped BigOperators

/-- A rational affine form in explicitly indexed variables. -/
structure Affine (n : ℕ) where
  constant : ℚ
  coeff : Fin n → ℚ

namespace Affine

variable {n : ℕ}

def const (c : ℚ) : Affine n := ⟨c, fun _ => 0⟩

def var (i : Fin n) : Affine n := ⟨0, fun j => if j = i then 1 else 0⟩

instance (k : ℕ) : OfNat (Affine n) k := ⟨const k⟩

instance : Add (Affine n) := ⟨fun a b => ⟨a.constant + b.constant, a.coeff + b.coeff⟩⟩

instance : Neg (Affine n) := ⟨fun a => ⟨-a.constant, -a.coeff⟩⟩

instance : Sub (Affine n) := ⟨fun a b => a + -b⟩

instance : SMul ℚ (Affine n) := ⟨fun c a => ⟨c * a.constant, fun i => c * a.coeff i⟩⟩

instance : HDiv (Affine n) ℚ (Affine n) := ⟨fun a c => c⁻¹ • a⟩

instance : SMul ℕ (Affine n) := ⟨fun c a => (c : ℚ) • a⟩

instance : HDiv (Affine n) ℕ (Affine n) := ⟨fun a c => a / (c : ℚ)⟩

instance : DecidableEq (Affine n) := by
  intro a b
  have h : (a.constant = b.constant ∧ ∀ i, a.coeff i = b.coeff i) ↔ a = b := by
    constructor
    · rintro ⟨hc, hi⟩
      cases a
      cases b
      cases hc
      cases funext hi
      rfl
    · rintro rfl
      exact ⟨rfl, fun _ => rfl⟩
  exact decidable_of_iff _ h

/-- Interpret the rational coefficients and assignment in the reals. -/
noncomputable def eval (x : Fin n → ℝ) (a : Affine n) : ℝ :=
  (a.constant : ℝ) + ∑ i, (a.coeff i : ℝ) * x i

@[simp] theorem eval_const (x : Fin n → ℝ) (c : ℚ) : eval x (const c) = c := by
  simp [eval, const]

@[simp] theorem eval_zero (x : Fin n → ℝ) : eval x (0 : Affine n) = 0 := by
  change eval x (const 0) = 0
  simp

@[simp] theorem eval_one (x : Fin n → ℝ) : eval x (1 : Affine n) = 1 := by
  change eval x (const 1) = 1
  simp

@[simp] theorem eval_var (x : Fin n → ℝ) (i : Fin n) :
    eval x (var i) = x i := by
  classical
  simp [eval, var, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]

@[simp] theorem eval_add (x : Fin n → ℝ) (a b : Affine n) :
    eval x (a + b) = eval x a + eval x b := by
  change (↑(a.constant + b.constant) : ℝ) +
    (∑ i, (↑(a.coeff i + b.coeff i) : ℝ) * x i) = _
  simp only [eval, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  ring

@[simp] theorem eval_neg (x : Fin n → ℝ) (a : Affine n) :
    eval x (-a) = -eval x a := by
  change (↑(-a.constant) : ℝ) + (∑ i, (↑(-a.coeff i) : ℝ) * x i) = _
  simp only [eval, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_add]

@[simp] theorem eval_sub (x : Fin n → ℝ) (a b : Affine n) :
    eval x (a - b) = eval x a - eval x b := by
  change eval x (a + -b) = _
  simp [sub_eq_add_neg]

@[simp] theorem eval_smul (x : Fin n → ℝ) (a : Affine n) (c : ℚ) :
    eval x (c • a) = (c : ℝ) * eval x a := by
  simp [eval, HSMul.hSMul, SMul.smul, mul_assoc, Finset.mul_sum, mul_add]

@[simp] theorem eval_div (x : Fin n → ℝ) (a : Affine n) (c : ℚ) :
    eval x (a / c) = eval x a / (c : ℝ) := by
  change eval x (c⁻¹ • a) = _
  simp [div_eq_mul_inv, mul_comm]

@[simp] theorem eval_nsmul (x : Fin n → ℝ) (a : Affine n) (c : ℕ) :
    eval x (c • a) = (c : ℝ) * eval x a := by
  change eval x ((c : ℚ) • a) = _
  simp

@[simp] theorem eval_natDiv (x : Fin n → ℝ) (a : Affine n) (c : ℕ) :
    eval x (a / c) = eval x a / (c : ℝ) := by
  change eval x (a / (c : ℚ)) = _
  simp

end Affine

/-- A list of row indices and their rational multipliers. -/
abbrev Multipliers := List (ℕ × ℚ)

/-- The weighted sum of the requested rows. A missing row is detected separately. -/
def combine {n : ℕ} (rows : List (Affine n)) : Multipliers → Affine n
  | [] => 0
  | (i, c) :: rest => c • (rows[i]?.getD 0) + combine rows rest

/-- Check valid row indices, nonnegative multipliers and exact equality to the target. -/
def check {n : ℕ} (rows : List (Affine n)) (weights : Multipliers) (target : Affine n) : Bool :=
  weights.all (fun p => decide (p.1 < rows.length ∧ 0 ≤ p.2)) &&
    decide (combine rows weights = target)

theorem combine_nonneg {n : ℕ} (x : Fin n → ℝ) (rows : List (Affine n))
    (weights : Multipliers)
    (hWeights : ∀ p ∈ weights, p.1 < rows.length ∧ 0 ≤ p.2)
    (hRows : ∀ row ∈ rows, 0 ≤ row.eval x) :
    0 ≤ (combine rows weights).eval x := by
  induction weights with
  | nil => simp [combine]
  | cons p rest ih =>
    obtain ⟨i, c⟩ := p
    obtain ⟨hi, hc⟩ := hWeights (i, c) (List.mem_cons_self ..)
    have hrow : 0 ≤ (rows[i]'hi).eval x := hRows _ (List.getElem_mem hi)
    have hrest : 0 ≤ (combine rows rest).eval x :=
      ih (fun p hp => hWeights p (List.mem_cons_of_mem _ hp))
    simp [combine, List.getElem?_eq_getElem hi]
    exact add_nonneg (mul_nonneg (by exact_mod_cast hc) hrow) hrest

/-- Every real assignment satisfying the checked rows also satisfies the target. -/
theorem check_sound {n : ℕ} {rows : List (Affine n)} {weights : Multipliers}
    {target : Affine n} (h : check rows weights target = true)
    (x : Fin n → ℝ) (hRows : ∀ row ∈ rows, 0 ≤ row.eval x) :
    0 ≤ target.eval x := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rw [← h.2]
  exact combine_nonneg x rows weights h.1 hRows

/-- The published certificates derive either the constant −1 or the negative of the
positive slack variable. -/
structure Certificate where
  useGap : Bool
  weights : Multipliers

def Certificate.target {n : ℕ} (cert : Certificate) (gap : Affine n) : Affine n :=
  if cert.useGap then -gap else -1

/-- Pair the systems and certificates in their published order. Match the list lengths
exactly so that a missing branch or certificate makes the checker return false. -/
def checkBatch {n : ℕ} (gap : Affine n) :
    List (List (Affine n)) → List Certificate → Bool
  | [], [] => true
  | rows :: systems, cert :: certs =>
    check rows cert.weights (cert.target gap) && checkBatch gap systems certs
  | _, _ => false

/-- A checked batch excludes each listed branch when the real slack is positive. -/
theorem checkBatch_sound {n : ℕ} {gap : Affine n} {systems : List (List (Affine n))}
    {certs : List Certificate} (h : checkBatch gap systems certs = true)
    {rows : List (Affine n)} (hMem : rows ∈ systems) (x : Fin n → ℝ)
    (hRows : ∀ row ∈ rows, 0 ≤ row.eval x) (hGap : 0 < gap.eval x) : False := by
  induction systems generalizing certs with
  | nil => simp at hMem
  | cons system systems ih =>
    cases certs with
    | nil => simp [checkBatch] at h
    | cons cert certs =>
      simp only [checkBatch, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hMem with rfl | hMem
      · have h := check_sound h.1 x hRows
        cases ht : cert.useGap
        · have hBad : (1 : ℝ) ≤ 0 := by simpa [Certificate.target, ht] using h
          exact (not_le_of_gt zero_lt_one) hBad
        · have hBad : gap.eval x ≤ 0 := by simpa [Certificate.target, ht] using h
          exact (not_le_of_gt hGap) hBad
      · exact ih h.2 hMem

private def readWeight (token : String) : Option (ℕ × ℚ) := do
  let [index, numerator, denominator] := token.splitOn ":" | none
  let i ← index.toNat?
  let p ← numerator.toNat?
  let q ← denominator.toNat?
  if q = 0 then none else some (i, (p : ℚ) / (q : ℚ))

private def readCertificate (line : String) : Option Certificate := do
  let target :: weights := line.splitOn " " | none
  let useGap ←
    match target with
    | "g" => some true
    | "1" => some false
    | _ => none
  let values ← weights.mapM readWeight
  pure ⟨useGap, values⟩

/-- Decode the published rational certificate data. Malformed entries cause failure. -/
def decode (data : String) : Option (List Certificate) :=
  (data.splitOn "\n").mapM readCertificate

/-- Check an encoded certificate batch without relying on the importer. -/
def checkEncoded {n : ℕ} (gap : Affine n) (systems : List (List (Affine n)))
    (data : String) : Bool :=
  match decode data with
  | none => false
  | some certs => checkBatch gap systems certs

/-- A checked encoded batch excludes every listed branch over the reals. -/
theorem checkEncoded_sound {n : ℕ} {gap : Affine n} {systems : List (List (Affine n))}
    {data : String} (h : checkEncoded gap systems data = true)
    {rows : List (Affine n)} (hMem : rows ∈ systems) (x : Fin n → ℝ)
    (hRows : ∀ row ∈ rows, 0 ≤ row.eval x) (hGap : 0 < gap.eval x) : False := by
  cases hd : decode data with
  | none => simp [checkEncoded, hd] at h
  | some certs =>
    have hc : checkBatch gap systems certs = true := by simpa [checkEncoded, hd] using h
    exact checkBatch_sound hc hMem x hRows hGap

end ZetaSixth.Exponents.Farkas
