import SevenCycle.Adjacent.Stage6.Data
import SevenCycle.Adjacent.UnionMasks
import SevenCycle.Proof.Frame

/-! Soundness of each fixed-union obstruction on one of its remaining marked bands. -/

namespace SevenCycle.Adjacent.Stage6

open Proof Blueprint Blueprint.SearchSpec SlabJoin FrameGeometry

private def sites : Array (Tuple 4) := (Array.range 2401).map position

private theorem mem_sites (x : Tuple 4) : x ∈ sites :=
  Array.mem_map.mpr ⟨address x, Array.mem_range.mpr (UnionMasks.components x).1, (UnionMasks.components x).2⟩

private def inside (bits : Nat) : Array (Tuple 4) :=
  ((Array.range 2401).filter bits.testBit).map position

private theorem mem_inside {bits : Nat} {D : Points} (hd : Stores bits D) (x : Tuple 4) :
    x ∈ inside bits ↔ x ∈ D := by
  constructor
  · intro hx
    obtain ⟨j,hj,rfl⟩ := Array.mem_map.mp hx
    exact ((hd j).mp (Array.mem_filter.mp hj).2).2
  · intro hx
    have hc := UnionMasks.components x
    have hbit := (hd (address x)).mpr ⟨hc.1, by rw [hc.2]; exact hx⟩
    exact Array.mem_map.mpr ⟨address x,Array.mem_filter.mpr ⟨Array.mem_range.mpr hc.1,hbit⟩,hc.2⟩

private def forced (ds : Array (Tuple 4)) (k : Axis) (s : Height) : Array (Tuple 4) :=
  (ds.filter (fun x => x k == s || x k == s+1)).map (fun x => setHeight x k 0)

private theorem mem_forced {bits : Nat} {D : Points} (hd : Stores bits D) (k : Axis) (s : Height) (y : Tuple 4) :
    y ∈ forced (inside bits) k s ↔ y ∈ stripe D k s := by
  rw [stripe, mem_face]
  simp [forced, mem_inside hd, and_assoc]

private def inMarkedUnion (m : Frame) (y : Tuple 4) : Bool :=
  (Array.finRange 4).any fun k =>
    let c := start m k true
    m.gap k == 1 && (y k == m.base k || y k == c || y k == c+1)

private theorem inMarkedUnion_iff (m : Frame) (y : Tuple 4) :
    inMarkedUnion m y = true ↔ inUnion m y := by
  simp only [inMarkedUnion, Array.any_eq_true', Bool.and_eq_true, Bool.or_eq_true_iff,
    beq_iff_eq, inUnion, inSlab, Finset.mem_insert, Finset.mem_singleton, or_assoc]
  constructor
  · rintro ⟨k,_,h⟩
    exact ⟨k,h⟩
  · rintro ⟨k,h⟩
    exact ⟨k,Array.mem_ofFn.mpr ⟨k,rfl⟩,h⟩

private def freer (ds fs : Array (Tuple 4)) (m : Frame) (k : Axis) (s : Height) (y : Tuple 4) : Bool :=
  (y k == 0) && !inMarkedUnion m y &&
    !(fs.any (near y)) &&
    (!(ds.any (near (setHeight y k s))) || !(ds.any (near (setHeight y k (s+1)))))

/-- The marked band must have 33 words. The certificate rules out enough
additional points to attain this size after its prescribed stripe is included. -/
def checkBand (m : Frame) (r : Row) : Bool :=
  let s := start m r.axis r.later
  let ds := inside r.mask
  let fs := forced ds r.axis s
  (m.gap r.axis != 1) && checkTree r.tree (sites.filter (freer ds fs m r.axis s)) (33-fs.size)

theorem checkBand_sound (m : Frame) (r : Row) (ok : checkBand m r = true)
    {D : Points} (hd : Stores r.mask D) (W : Family) : ¬ Remaining m D W := by
  intro hw
  obtain ⟨hk,htree⟩ := Bool.and_eq_true_iff.mp ok
  let k := r.axis
  let s := start m k r.later
  let B := W k r.later
  let ds := inside r.mask
  let fs := forced ds k s
  let X := B.filter (fun y => ¬ inUnion m y)
  obtain ⟨hface, hfixed, hlift⟩ := hw.2 k (bne_iff_ne.mp hk) r.later
  change B.filter (inUnion m) = stripe D k s at hfixed
  have hxCode : packing cycleStep X := fun x hx y hy =>
    hface.2.1 x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
  have hsub (y : Tuple 4) (hy : y ∈ X) : y ∈ sites.filter (freer ds fs m k s) := by
    obtain ⟨hyB,hout⟩ := Finset.mem_filter.mp hy
    have hfar : fs.any (near y) = false := by
      apply Bool.eq_false_iff.mpr
      intro bad
      obtain ⟨z,hz,close⟩ := Array.any_eq_true'.mp bad
      have Hz : z ∈ B.filter (inUnion m) := hfixed ▸ (mem_forced hd k s z).mp hz
      obtain ⟨HzB,hin⟩ := Finset.mem_filter.mp Hz
      exact hface.2.1 y hyB z HzB ⟨fun e => hout (e ▸ hin), (near_iff ..).mp close⟩
    obtain ⟨a,ha,hn,hsep⟩ := hlift y hyB hout
    have clear : ds.any (near (setHeight y k a)) = false := by
      apply Bool.eq_false_iff.mpr
      intro bad
      obtain ⟨z,hz,close⟩ := Array.any_eq_true'.mp bad
      have H := (mem_inside hd _).mp hz
      exact hsep z H ⟨fun e => hn (e ▸ H), (near_iff ..).mp close⟩
    have clearOne : (!(ds.any (near (setHeight y k s))) || !(ds.any (near (setHeight y k (s+1))))) = true := by
      change a = s ∨ a = s+1 at ha
      rcases ha with rfl | rfl <;> simp [clear]
    apply Array.mem_filter.mpr
    exact ⟨mem_sites y, by simp [freer,hface.2.2 y hyB,Bool.eq_false_iff.mpr (hout ∘ (inMarkedUnion_iff _ _).mp),hfar,clearOne]⟩
  have small := checkTree_sound r.tree _ (33-fs.size) htree X hxCode hsub
  have hlen : (B.filter (inUnion m)).card ≤ fs.size := by
    rw [hfixed]
    exact (Finset.card_le_card (show stripe D k s ⊆ fs.toList.toFinset from fun y hy =>
      List.mem_toFinset.mpr (Array.mem_toList_iff.mpr ((mem_forced hd k s y).mpr hy)))).trans ((by simpa using List.toFinset_card_le fs.toList))
  have hsum := Finset.card_filter_add_card_filter_not (s := B) (inUnion m)
  have hcard : B.card = 33 := hface.1
  change (B.filter (inUnion m)).card + X.card = B.card at hsum
  omega

def rowsCheck (p : Bool) : Bool :=
  (Array.finRange (rowCount p)).all fun i => checkBand (frame p) (row p i)

theorem rowsCheck_sound (p : Bool) (ok : rowsCheck p = true) (i : Fin (rowCount p))
    {D : Points} (hd : Stores (rowMask p i) D) (W : Family) : ¬ Remaining (frame p) D W :=
  checkBand_sound _ _ (Array.all_eq_true'.mp ok i (Array.mem_ofFn.mpr ⟨i,rfl⟩)) hd W

end SevenCycle.Adjacent.Stage6
