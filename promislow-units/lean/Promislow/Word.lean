import Promislow.Units
namespace Promislow
noncomputable section

abbrev Word := List (Letter × Bool)
def reverseWord (w : Word) : Word := w.reverse.map fun (l,r) => (l,!r)
def commList (u v : Word) : Word := u++v++reverseWord u++reverseWord v
def wa : Word := commList [(.A,false)] [(.B,false)]
def wb : Word := commList [(.A',false)] [(.B,false)]
def whole : Word := commList (commList (commList wa wb) wa) wa

def wordN (w : Word) : IntegralGroupRing := (w.map fun (l,r) => N l r).prod
def wordD (w : Word) : IntegralGroupRing := (w.map fun (l,_) => F l ^ 4).prod

namespace Ambient
variable {S : Type*} [Ring S] (E : Ambient S)
def eval (w : Word) : Sˣ := (w.map fun (l,r) => signed (E.L l) r).prod

theorem eval_append (u v : Word) : E.eval (u++v) = E.eval u * E.eval v := by
  simp [eval]

theorem eval_reverse (u : Word) : E.eval (reverseWord u) = (E.eval u)⁻¹ := by
  induction u with
  | nil => simp [eval,reverseWord]
  | cons t xs ih =>
    rcases t with ⟨l,r⟩
    have flip : reverseWord ((l,r)::xs) = reverseWord xs ++ [(l,!r)] := by simp [reverseWord]
    rw [flip,E.eval_append,ih]
    cases r <;> simp [eval,signed]

theorem eval_comm (u v : Word) : E.eval (commList u v) = commWord (E.eval u) (E.eval v) := by
  simp only [commList,eval_append,eval_reverse,commWord]

theorem cleared (w : Word) :
    E.ι (wordD w)*(E.eval w:S) = E.ι (wordN w) := by
  induction w with
  | nil => simp [wordD,wordN,eval]
  | cons t xs ih =>
    rcases t with ⟨l,r⟩
    change E.ι (F l^4 * wordD xs) *
      (↑(signed (E.L l) r * E.eval xs):S) = E.ι (N l r * wordN xs)
    rw [map_mul,map_pow,Units.val_mul,E.letter_value,map_mul,← ih]
    change (E.f l^4*E.ι (wordD xs))*(E.ι (N l r)*↑(E.den l)⁻¹*(E.eval xs:S)) = _
    have cen (z : S) : Commute (E.ι (wordD xs)) z := by
      clear ih
      induction xs with
      | nil => simp [wordD,Commute]
      | cons t ys h =>
        rcases t with ⟨v,i⟩
        change Commute (E.ι (F v^4*wordD ys)) z
        rw [map_mul,map_pow]
        exact ((E.central v z).pow_left 4).mul_left h
    rw [← E.den_coe]
    simp only [mul_assoc,(cen (E.ι (N l r))).left_comm,
      (E.den_c l (E.ι (N l r))).left_comm,(E.den_c l (E.ι (wordD xs))).left_comm,
      Units.mul_inv_cancel_left]

end Ambient
end
end Promislow
