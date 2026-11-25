import SevenCycle.AtlasData
import SevenCycle.Proof.Witness
import Mathlib.Data.Fin.VecNotation

/-! # Checking the representatives in the released atlas -/

namespace SevenCycle.Atlas

open Proof

/-- The lexicographic list of points of the three-dimensional torus. -/
private def cubeWords : Array (Tuple 3) :=
  (Array.finRange 7).flatMap fun x =>
    (Array.finRange 7).flatMap fun y =>
      (Array.finRange 7).map fun z => ![x, y, z]

private theorem mem_cubeWords (w : Tuple 3) : w ∈ cubeWords := by
  have hm (i : Fin 7) : i ∈ Array.finRange 7 := Array.mem_ofFn.mpr ⟨i, rfl⟩
  apply Array.mem_flatMap.mpr
  refine ⟨w 0, hm _, Array.mem_flatMap.mpr ⟨w 1, hm _, Array.mem_map.mpr ⟨w 2, hm _, ?_⟩⟩⟩
  funext k
  fin_cases k <;> rfl

def hasWord (planes : Vector UInt64 7) (w : Tuple 3) : Bool :=
  (planes.get (w 0)).toNat.testBit (7 * (w 1).val + (w 2).val)

def decodedWords (planes : Vector UInt64 7) : Array (Tuple 3) :=
  cubeWords.filter (hasWord planes)

/-- The set represented by the bits in seven ordered planes. -/
def decodedSet (planes : Vector UInt64 7) : Finset (Tuple 3) :=
  Finset.univ.filter fun w => hasWord planes w

theorem decodedWords_set (planes : Vector UInt64 7) :
    rowSet (decodedWords planes) = decodedSet planes := by
  ext w
  simp only [rowSet, Finset.mem_image, Finset.mem_univ, true_and, decodedSet, Finset.mem_filter]
  have hmem : w ∈ decodedWords planes ↔ hasWord planes w := by
    simp [decodedWords, mem_cubeWords]
  rw [← hmem, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, hi⟩
  · rintro ⟨i, hi, hw⟩
    exact ⟨⟨i, hi⟩, hw⟩

/-- Expand set bits and check all pairs of array positions. -/
def rowCheck (planes : Vector UInt64 7) : Bool :=
  let words := decodedWords planes
  words.size == 33 && rowsCheck words

theorem rowCheck_sound (planes : Vector UInt64 7) (h : rowCheck planes = true) :
    packing cycleStep (decodedSet planes) ∧ (decodedSet planes).card = 33 := by
  obtain ⟨hsize, hpack⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hc, hp⟩ := rowsCheck_sound _ hpack
  rw [decodedWords_set] at hc hp
  exact ⟨hp, hc.trans (beq_iff_eq.mp hsize)⟩

/-- Apply the proved row checker to every supplied representative. -/
def rowsValid (rows : Array (Vector UInt64 7)) : Bool := rows.all rowCheck

theorem rowsValid_sound (rows : Array (Vector UInt64 7)) (h : rowsValid rows = true)
    (r : Fin rows.size) : packing cycleStep (decodedSet rows[r]) ∧
      (decodedSet rows[r]).card = 33 :=
  rowCheck_sound _ (Array.all_eq_true'.mp h _ (Array.mem_iff_getElem.mpr ⟨r, r.isLt, rfl⟩))

end SevenCycle.Atlas
