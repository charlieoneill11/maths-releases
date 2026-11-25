import HadwigerNelson.Certificate.Interval

/-! The two angular budgets and the box objective in §§8–9. The same formulas
can be evaluated over the reals or using rational interval operations. -/

namespace HadwigerNelson.Certificate.ParameterBoxes

class Operations (α : Type) extends Add α, Sub α, Mul α, Min α, Max α where
  constant : ℚ → α
  root : α → α
  intPart : α → α

open Operations

instance intervalOperations : Operations Interval where
  add := Interval.add
  sub := Interval.sub
  mul := Interval.mul
  min := Interval.minimum
  max := Interval.maximum
  constant := Interval.point
  root := Interval.sqrt
  intPart := Interval.floor

noncomputable instance realOperations : Operations ℝ where
  constant := Rat.cast
  root := Real.sqrt
  intPart x := (⌊x⌋ : ℤ)

abbrev order : ℚ := 10689
def pair (k : ℚ) := k*(k-1)/(order*(order-1))
def four (k : ℚ) := pair k*(k-2)*(k-3)/((order-2)*(order-3))

variable {α : Type} [Operations α]

/-- The expanded quadratic avoids cancellation when bounding V on a box. -/
def variance (m : α) : α :=
  let k : ℚ := 2090
  constant (order*(order-1)+(4*(266/9)*(k-2))/four k) -
    constant (24*pair k/four k-1)*m - constant (2/order)*(m*m)

def weighted (m v s j : α) (a b : ℚ) : α :=
  let w := constant a*s + constant b*j
  let norm := constant (a*a)*s + constant (b*b)*j - constant (1/order)*(w*w)
  constant (2/order)*m*w + root (constant 2*v*norm)

def chooseTwo (s : α) : α := constant (1/2)*s*(s-constant 1)

def pairLower (m : α) : α :=
  let k : ℚ := 1317
  let a := constant (order*(order-1)) + m - constant (2/order)*(m*m)
  constant 2*m - intPart (constant (1/(6*pair k))*
    (a*constant (four k) + constant ((266/9)*(k-2))))

/-- The seven upper bounds on disk occupancy, with outward integer floor. -/
def diskCount (i : Nat) := (10 + 2*(14+5*i))^2 / 100

def width (i : Nat) : ℚ := (if i=0 then 4 else 5)/10*(1837/250000)

def firstTerms (m s j v : α) : α :=
  let B : ℚ := 112668096940
  let nQ : ℚ := order*71152801254159
  let p : ℚ := 708385488148
  let base := constant nQ + m*constant (p-B) - s*constant 16034576942481 - j*constant 3057937052494
  let nr := constant order-s
  let loss := min (nr*constant 150296106235)
    (min (nr*constant 97911102803+j*constant 104770006866) (j*constant 300592212470))
  let modeR := base + constant B*weighted m v s j (828/1000) (1195/10000) + loss
  let modeD := base + constant B*weighted m v s j (828/1000) (6195/10000)
  constant (1/10^18) * min (constant nQ + m*constant p) (min modeR modeD)

def sumSeven (f : Nat → α) : α :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6

structure Budget (α : Type) where
  r : α
  d : α
  angle : α
  spare : α

def budgets (m s j h v : α) : Budget α :=
  let zero := constant 0
  let ld := weighted m v h zero 1 0
  let lr := weighted m v s zero 1 0
  let br := min lr (min (constant 5*s+chooseTwo s) (constant (1/2)*(lr+constant 5*s)))
  let bd := min ld (min (constant 14*s+constant 8*j+chooseTwo s) (constant (1/2)*(ld+constant 5*h)))
  let t := pairLower m
  let halfLD := constant (1/2)*ld
  let reserve := (m-br)*constant (53/10000) + (m-bd)*constant (1837/250000-53/10000)
  let rest := constant order-h
  let q := constant (355/113*order)-reserve
  let qd := constant (355/113)*rest-reserve+constant (1837/250000)*halfLD
  let excess := fun i extra =>
    let k := diskCount i
    let allowed := intPart (constant ((k-1:Nat)/2 : ℚ)*rest) +
      min (constant 2*ld) (constant (k:ℚ)*h + chooseTwo h)
    constant (width i)*max (constant 2*m-constant 2*t-allowed-extra) zero
  ⟨t-br-halfLD,t-bd-halfLD,min q qd,
   min (q-constant (1/2)*sumSeven (fun i => excess i zero))
     (qd-constant (1/2)*sumSeven (fun i => excess i ld))⟩

def credit (b : Budget α) (high low slope : ℚ) : α :=
  let z := constant 0
  max z (max (constant low*max b.r z + constant (high-low)*max b.d z - constant slope*b.angle)
    (constant low*b.r + constant (high-low)*b.d - constant slope*b.spare))

def objective (m s j h : α) : α :=
  let v := variance m
  let b := budgets m s j h v
  firstTerms m s j v - max (credit b (230/10^10) (79/10^10) (980/10^10))
    (credit b (259/10^10) (93/10^10) (1100/10^10))

end HadwigerNelson.Certificate.ParameterBoxes
