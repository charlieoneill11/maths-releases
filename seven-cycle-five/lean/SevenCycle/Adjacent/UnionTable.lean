import SevenCycle.Adjacent.Exterior
import SevenCycle.Adjacent.UnionData

namespace SevenCycle.Adjacent.UnionTable

open Proof Blueprint Blueprint.SearchSpec

private def digit (ch : UInt8) : ℕ :=
  let n := ch.toNat
  if 65 ≤ n ∧ n ≤ 90 then n-65
  else if 97 ≤ n ∧ n ≤ 122 then n-97+26
  else if 48 ≤ n ∧ n ≤ 57 then n-48+52
  else if n = 45 then 62 else 63

private def field (buf : ByteArray) (i : ℕ) : ℕ :=
  64 * digit (buf.get! (2*i)) + digit (buf.get! (2*i+1))

private def point (n : ℕ) : Tuple 4 := ![↑(n/343), ↑(n/49%7), ↑(n/7%7), ↑(n%7)]

private def box (n : ℕ) : Tuple 4 :=
  ![↑(n/27+2), ↑(n/9%3+2), ↑(n/3%3+2), ↑(n%3+2)]

def decode (row : String) : Adjacent.Exterior.Certificate :=
  let b := row.toUTF8
  let n := field b 0
  let inner := (Array.range n).map fun i => point (field b (1+i))
  let boxes := (Array.range (b.size/2-1-n)).map fun i => box (field b (1+n+i))
  ⟨fun _ => 6, inner, boxes⟩

private def index (a b c d : ℕ) : ℕ := 64*a + 16*b + 4*c + d

private def axes (base z : Height) (isBox : Bool) : Array ℕ :=
  (Array.range 4).filter fun i =>
    let x := base + 3 + (i : Height)
    if isBox then x == z || x == z+1
    else x == z || x == z+1 || x == z-1

private def markSites (out : Array ℕ) (base z : Tuple 4) (j : ℕ) (isBox : Bool) :
    Array ℕ := Id.run do
  let xs := axes (base 0) (z 0) isBox
  let ys := axes (base 1) (z 1) isBox
  let zs := axes (base 2) (z 2) isBox
  let ws := axes (base 3) (z 3) isBox
  let mut marked := out
  for a in xs do
    for b in ys do
      for c in zs do
        for d in ws do
          marked := marked.setIfInBounds (index a b c d) j
  return marked

/-- Generate candidate blocker indices from the decoded points and boxes. The
proof independently checks the selected index at each of the 256 sites. -/
private def hints (cert : Adjacent.Exterior.Certificate) : Array ℕ := Id.run do
  let mut out := Array.replicate 256 (cert.inside.size + cert.boxes.size)
  for h : j in [:cert.inside.size] do
    out := markSites out cert.base cert.inside[j] j false
  for h : j in [:cert.boxes.size] do
    out := markSites out cert.base cert.boxes[j] (cert.inside.size + j) true
  return out

def checkRow (row : String) : Bool :=
  let cert := decode row
  let guesses := hints cert
  Adjacent.Exterior.choiceCheck cert fun d =>
    guesses[index (d 0).val (d 1).val (d 2).val (d 3).val]!

def windowCheck (rows : Array String) (interval : ℕ × ℕ) : Bool :=
  (rows.extract interval.1 interval.2).all checkRow

theorem windowCheck_sound (rows : Array String) (interval : ℕ × ℕ) (ok : windowCheck rows interval = true)
    (i : Fin rows.size) (hlo : interval.1 ≤ i.val) (hhi : i.val < interval.2)
    (m : Frame) (hb : m.base = fun _ => 6) (hg : ∀ k, m.gap k = 1) (E : Points)
    (he : SearchSpec.Exterior m (rowSet (decode (rows[i.val]'i.isLt)).inside) E) :
    (rowSet (decode (rows[i.val]'i.isLt)).inside ∪ E).card ≤ 112 := by
  apply Adjacent.Exterior.check_sound _ _ m hb hg E he
  apply Adjacent.Exterior.check_of_choiceCheck
  apply Array.all_eq_true_iff_forall_mem.mp ok
  apply Array.mem_extract_iff_getElem.mpr
  have inside : i.val < min interval.2 rows.size := lt_min hhi i.isLt
  refine ⟨i.val - interval.1, Nat.sub_lt_sub_right hlo inside, ?_⟩
  simp only [Nat.add_sub_of_le hlo]

end SevenCycle.Adjacent.UnionTable
