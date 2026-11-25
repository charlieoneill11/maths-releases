import SevenCycle.Atlas.LeafData
import SevenCycle.Bitsets.Orbit
import SevenCycle.Blueprint.Definitions
import Std.Data.HashMap.Basic

/-!
# Certifying the orbit of a normalized leaf

A hash selects a hint. Acceptance compares all seven planes to a signed
permutation and translation of a particular row of the atlas. Soundness
does not depend on uniqueness of fingerprints or completeness of the hints.
-/
namespace SevenCycle.Atlas.Leaves
open Bitsets Proof Blueprint

private def digit (ch : UInt8) : UInt64 :=
  let n := ch.toUInt64
  if 65 ≤ n ∧ n ≤ 90 then n-65
  else if 97 ≤ n ∧ n ≤ 122 then n-97+26
  else if 48 ≤ n ∧ n ≤ 57 then n-48+52
  else if n = 45 then 62 else 63

private def field (bytes : ByteArray) (start count : ℕ) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for j in [start:start+count] do
    v := (v <<< 6) ||| digit (bytes.get! j)
  return v

private def hints : Std.HashMap UInt64 ℕ := Id.run do
  let mut m := Std.HashMap.emptyWithCapacity 6535
  for block in LeafData.blocks do
    let bytes := block.toUTF8
    for j in [:bytes.size/14] do
      m := m.insert (field bytes (14*j) 10) (field bytes (14*j+10) 4).toNat
  return m

private def fingerprint (c : Cube) : UInt64 :=
  (c.toArray.foldl (fun h p => (h ^^^ p) * 1099511628211) 14695981039346656037) &&& 1152921504606846975

private def motion (m : ℕ) : Blueprint.Isometry 3 :=
  (perm3 (Fin.ofNat 6 (m/2744)), sign3 (Fin.ofNat 8 (m/343)),
    ![↑(m/49%7), ↑(m/7%7), ↑(m%7)])

private def checkHint (rows : Array Cube) (c : Cube) (hint : Option ℕ) : Bool :=
  match hint with
  | none => false
  | some w =>
    let r := w/16464
    if hr : r < rows.size then cubeAct (motion (w%16464)) rows[r] == c else false

private theorem matches_sound (rows : Array Cube) (c : Cube) (hint : Option ℕ)
    (ok : checkHint rows c hint = true) :
    ∃ r : Fin rows.size, ∃ g : Blueprint.Isometry 3,
      cubeSet c = actOnCode g (cubeSet rows[r]) := by
  cases hint with
  | none => contradiction
  | some w =>
    simp only [checkHint] at ok
    split at ok
    · rename_i hr
      have eq := beq_iff_eq.mp ok
      refine ⟨⟨_,hr⟩, motion (w%16464), ?_⟩
      rw [← eq]
      exact cubeSet_act _ _
    · contradiction

/-- Look up an isometry witness and compare every bit of the leaf. -/
def atlasLeaf (c : Cube) : Bool := checkHint atlasPlanes c hints[fingerprint c]?

theorem atlasLeaf_sound (c : Cube) (ok : atlasLeaf c = true) :
    ∃ r : Fin atlasPlanes.size, ∃ g : Blueprint.Isometry 3,
      cubeSet c = actOnCode g (atlasRepresentative r) :=
  matches_sound atlasPlanes c _ ok

end SevenCycle.Atlas.Leaves
