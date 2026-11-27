import Promislow.Word
import Lean.Data.Json.FromToJson.Basic

open Lean Elab Term in
private def certificateField (key : String) : TermElabM Json := do
  let raw := include_str "../../code/integral-pair.json"
  let .ok json := Json.parse raw | throwError "invalid certificate JSON"
  let .ok field := json.getObjVal? key | throwError "missing certificate field {key}"
  return field

open Lean Elab Term in
elab "certificateCodes%" key:str : term => do
  let field ← certificateField key.getString
  let .ok ns := (fromJson? field : Except String (List Int)) | throwError "expected signed integers"
  unless ns.all (fun n => [1,2,3,-1,-2,-3].contains n) do
    throwError "invalid signed letter in certificate"
  return toExpr ns

open Lean Elab Term in
elab "certificateParameters%" : term => do
  let .ok rows := (← certificateField "vertices").getArr? | throwError "expected vertices"
  let mut vertices : List (Nat × String × Int) := []
  for row in rows do
    let .arr #[m,axis,spacing] := row | throwError "expected a vertex triple"
    let .ok n := m.getNat? | throwError "expected a cyclotomic index"
    let .ok s := axis.getStr? | throwError "expected an axis"
    let .ok k := spacing.getInt? | throwError "expected an integral spacing"
    vertices := (n,s,k)::vertices
  let .ok phases := (fromJson? (← certificateField "phases") : Except String (List (Int × Int)))
    | throwError "expected phase pairs"
  let .ok powers := (fromJson? (← certificateField "centered_denominator_powers") : Except String (List Nat))
    | throwError "expected denominator powers"
  return toExpr (vertices.reverse,phases,powers)

namespace Promislow
def decode (n : ℤ) : Letter × Bool :=
  (if n.natAbs=1 then .A else if n.natAbs=2 then .A' else .B, n<0)
def recordedU : Word := (certificateCodes% "u").map decode
def recordedV : Word := (certificateCodes% "v").map decode

private def recordedParameters : List (ℕ × String × ℤ) × List (ℤ × ℤ) × List ℕ :=
  certificateParameters%

/-- The vertices, phases and three denominator exponents in the artifact match
the letter definitions and both signed words, including multiplicities. -/
theorem recorded_parameters :
    let letters := [Letter.A, .A', .B]
    let params := letters.map fun l =>
      (2*l.degree+1, if l.axis = .x then "a" else "b", l.spacing)
    let powers := fun (w : Word) => letters.map fun l => 4 * w.countP (fun t => t.1=l)
    recordedParameters = (params,Sparse.phases,powers recordedU) ∧
      powers recordedV = powers recordedU := by decide +kernel

def pushLetter (t : Letter × Bool) : Word → Word
  | [] => [t]
  | s::ss => if s=(t.1,!t.2) then ss else t::s::ss

def reduceWord (w : Word) := w.foldr pushLetter []

theorem recorded_reductions : reduceWord whole=recordedU ∧ reverseWord recordedU=recordedV := by
  decide +kernel

namespace Ambient
variable {S : Type*} [Ring S] (E : Ambient S)
theorem eval_push (t : Letter×Bool) (w : Word) :
    E.eval (pushLetter t w) = signed (E.L t.1) t.2 * E.eval w := by
  rcases t with ⟨l,r⟩
  cases w with
  | nil => simp [pushLetter,eval]
  | cons s xs =>
    by_cases h : s=(l,!r)
    · subst s
      cases r <;> simp [pushLetter,eval,signed]
    · simp [pushLetter,h,eval]

theorem eval_reduced (w : Word) : E.eval (reduceWord w) = E.eval w := by
  induction w with
  | nil => rfl
  | cons t xs ih =>
    change E.eval (pushLetter t (reduceWord xs)) = _
    rw [E.eval_push,ih]
    rfl

end Ambient
end Promislow
