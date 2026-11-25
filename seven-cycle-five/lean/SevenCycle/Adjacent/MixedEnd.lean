import SevenCycle.Native.MixedSlabJoins
import SevenCycle.Adjacent.Stage6.Verified
import SevenCycle.Adjacent.Slabs

/-! Fixed-frame terminal exclusions for the three mixed slab tables with surviving rows. -/

namespace SevenCycle.Adjacent.MixedEnd

open Blueprint Proof Blueprint.SearchSpec SlabJoin
open MixedSlabs (Covers Profile)

def twoProfile (p : Bool) : Profile := if p then #v[1,1,2,3] else #v[1,1,2,2]
def twoRows (p : Bool) : Array String := if p then MixedSlabData.rows1123 else MixedSlabData.rows1122

theorem three {C : Points} (hc : packing cycleStep C)
    (cover : ∀ k : Fin 4, (#v[1,1,1,2] : Profile).get k = 1 →
      Covers #v[1,1,1,2] MixedSlabData.rows1112 k (C.filter (inThree k))) : False := by
  obtain ⟨_,_,_,_,_,_,bad⟩ := MixedSlabs.three_sound C hc _ _ (fun _ => false) rfl
    (cover 0 rfl) (cover 1 rfl) (cover 2 rfl) Native.mixed1112_slab_join
  contradiction

private theorem within (p : Bool) (x : Tuple 4) :
    inUnion (Stage6.frame p) x ↔ inThree 0 x ∨ inThree 1 x := by
  have gap (k : Axis) : (Stage6.frame p).gap k = 1 ↔ k = 0 ∨ k = 1 := by
    fin_cases k <;> cases p <;> decide
  have slab (k : Axis) (hd : (Stage6.frame p).gap k = 1) : inSlab (Stage6.frame p) k x ↔ inThree k x := by
    have base : (Stage6.frame p).base k = 6 := by
      change -((Stage6.frame p).gap k : Height) = 6
      rw [hd]; decide
    have mid : start (Stage6.frame p) k true = 0 := by rw [start,if_pos rfl,base,hd]; decide
    simp [inSlab,base,mid,inThree]
  constructor
  · rintro ⟨k,hk,hx⟩
    have hi := (slab k hk).mp hx
    rcases (gap k).mp hk with rfl|rfl <;> tauto
  · rintro (hx|hx)
    · exact ⟨0,(gap 0).mpr (Or.inl rfl),(slab 0 ((gap 0).mpr (Or.inl rfl))).mpr hx⟩
    · exact ⟨1,(gap 1).mpr (Or.inr rfl),(slab 1 ((gap 1).mpr (Or.inr rfl))).mpr hx⟩

theorem two (p : Bool) {C : Points} (hc : packing cycleStep C) (hm : Marked (Stage6.frame p) C)
    (cover : ∀ k : Fin 4, (twoProfile p).get k = 1 →
      Covers (twoProfile p) (twoRows p) k (C.filter (inThree k))) : False := by
  let test := fun b => (Stage6.maskTable p).contains (FrameMask.mk b)
  have ok : MixedSlabs.check (twoProfile p) (twoRows p) test = true := by
    cases p
    · exact Native.mixed1122_slab_join
    · exact Native.mixed1123_slab_join
  obtain ⟨s,t,hs,ht,hit⟩ := MixedSlabs.two_sound C hc _ _ test
    (by cases p <;> decide : (twoProfile p).get 2 ≠ 1)
    (cover 0 (by cases p <;> rfl)) (cover 1 (by cases p <;> rfl)) ok
  obtain ⟨i,e⟩ := Stage6.maskTable_sound p (s ||| t) hit
  have hd : Stores (s ||| t) (C.filter (inUnion (Stage6.frame p))) := by
    intro j
    rw [Nat.testBit_or,Bool.or_eq_true_iff,hs,ht]
    simp only [Finset.mem_filter, within]
    tauto
  exact Stage6.noRemaining p i (e ▸ hd) _ (remaining hc hm)

end SevenCycle.Adjacent.MixedEnd
