import SevenCycle.Adjacent.LocalView
import SevenCycle.Adjacent.CertifiedJoin
import SevenCycle.Adjacent.FrameTransport

namespace SevenCycle.Adjacent.CommonFrame

open Blueprint Proof SearchSpec SlabJoin SlabReconstruction

private def order (g h : Isometry 4) : AxisOrder := Vector.ofFn fun i => h.1.symm (g.1 i)

private def signs (g h : Isometry 4) := signCode fun i => (g.2.1 i) ^^ (h.2.1 ((order g h)[i]))

private def around (s : Bool) (origin t : ZMod 7) : ZMod 7 := if s then -(t-origin) else t-origin

private theorem view_at (g : Isometry 4) (cs : Centers) (origin : Tuple 4)
    (h : View g cs origin = fun _ => 0) (x : Tuple 4) (j : Fin 4) :
    View g cs x j = around (g.2.1 j) (origin (g.1 j)) (x (g.1 j)) := by
  have arith : ∀ (s : Bool) (a b x t : ZMod 7), (if s then -a else a) + b - t = 0 →
      (if s then -x else x) + b - t = around s a x := by decide +kernel
  exact arith _ _ _ _ _ (congrFun h j)

private theorem corresponding (origin : Tuple 4) (g h : Isometry 4) (cg ch : Centers)
    (hg : View g cg origin = fun _ => 0) (hh : View h ch origin = fun _ => 0) (x : Tuple 4) :
    signedAction (order g h) (signs g h) (View h ch x) = View g cg x := by
  funext i
  have perm : h.1 ((order g h)[i]) = g.1 i := by simp [order]
  have bools : ∀ (a b : Bool) (u v : ZMod 7),
      (if a ^^ b then -(around b u v) else around b u v) = around a u v := by
    intro a b u v; cases a <;> cases b <;> simp [around]
  change (if (signs g h).val.testBit i then _ else _) = _
  rw [signs, sign_bit, view_at h ch origin hh, view_at g cg origin hg,perm]
  exact bools _ _ _ _

/-- If each anchor can be normalized in turn to one source row, the
normalization of coordinate zero furnishes a single frame for the complete
1111 join. The other three slabs use only their permitted signed permutations. -/
theorem coverage (C : Points) (origin : Tuple 4) (rows : Array String)
    (g : Axis → Isometry 4) (cs : Axis → Centers) (anchor : ∀ k, (g k).1 0 = k)
    (centered : ∀ k, View (g k) (cs k) origin = fun _ => 0)
    (record : ∀ k, ∃ r ∈ rows, (normSlab (actOnCode (g k) C)).image (center (cs k)) = rowPoints r)
    (i : Fin 4) : ComesFrom rows i ((C.image (View (g 0) (cs 0))).filter (inThree i)) := by
  let k := (g 0).1 i
  obtain ⟨r,hr,hit⟩ := record k
  let p := order (g 0) (g k)
  let s := signs (g 0) (g k)
  have pi (j : Fin 4) : p[j] = (g k).1.symm ((g 0).1 j) := by simp [p, order]
  have normal : p[i] = 0 := (pi i).trans ((g k).1.symm_apply_eq.mpr (anchor k).symm)
  have inj : Function.Injective (fun j : Fin 4 => p[j]) := by
    intro a b e
    change p[a] = p[b] at e
    rw [pi,pi] at e
    exact (g 0).1.injective ((g k).1.symm.injective e)
  have first (hi : i = 0) : p = identityOrder ∧ s.val = 0 := by
    have eq : k = 0 := (congrArg (g 0).1 hi).trans (anchor 0)
    constructor
    · apply Vector.ext
      intro n hn
      change p[(⟨n,hn⟩ : Fin 4)] = identityOrder[(⟨n,hn⟩ : Fin 4)]
      rw [pi,eq,Equiv.symm_apply_apply]
      exact identityIndex ⟨n,hn⟩
    · simp only [s,signs,eq]
      simp [order,signCode]
  have mapping (x : Tuple 4) : signedAction p s (View (g k) (cs k) x) = View (g 0) (cs 0) x :=
    corresponding origin _ _ _ _ (centered 0) (centered k) x
  have win (x : Tuple 4) : inThree i (View (g 0) (cs 0) x) ↔ inThree 0 (View (g k) (cs k) x) := by
    rw [← mapping]
    have near : ∀ (b : Bool) (z : ZMod 7), let v := if b then -z else z
      (v = 6 ∨ v = 0 ∨ v = 1) ↔ (z = 6 ∨ z = 0 ∨ z = 1) := by decide
    simpa only [inThree, signedAction, normal] using near (s.val.testBit i) (View (g k) (cs k) x 0)
  have eq : ((C.image (View (g 0) (cs 0))).filter (inThree i)) = (rowPoints r).image (signedAction p s) := by
    rw [← hit]
    ext w
    constructor
    · intro hw
      obtain ⟨hw,hin⟩ := Finset.mem_filter.mp hw
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr ⟨_, (mem_local _ _ _ _).mpr ⟨x,hx,(win _).mp hin,rfl⟩,mapping x⟩
    · intro hw
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨x,hx,hwin,rfl⟩ := (mem_local _ _ _ _).mp hz
      rw [mapping]
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,(win _).mpr hwin⟩
  rw [eq]
  exact comesFrom_image hr p s inj normal first

theorem card_le_of_record (C : Points) (hc : packing cycleStep C) (origin : Tuple 4)
    (g : Axis → Isometry 4) (cs : Axis → Centers) (anchor : ∀ k, (g k).1 0 = k)
    (centered : ∀ k, View (g k) (cs k) origin = fun _ => 0)
    (record : ∀ k, ∃ r ∈ SlabData.rows,
      (normSlab (actOnCode (g k) C)).image (center (cs k)) = rowPoints r) : C.card ≤ 112 := by
  have h := framed1111_bound (view_packing hc (g 0) (cs 0)) centred rfl (fun _ => rfl)
    (coverage C origin SlabData.rows g cs anchor centered record)
  rwa [Finset.card_image_of_injective _ (view_injective _ _)] at h

end SevenCycle.Adjacent.CommonFrame
