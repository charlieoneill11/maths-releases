import ZetaSixth.ExponentProofs.Farkas

namespace ZetaSixth.Exponents.CertificateSystems

open Farkas

abbrev Form := Affine 12

def s : Form := .var 0
def g : Form := .var 1
def r : Form := .var 2
def tail : Form := .var 3
def i : Form := .var 4
def z : Form := .var 5
def x : Form := .var 6
def E : Form := .var 7
def m : Form := .var 8
def n : Form := .var 9
def w : Form := .var 10
def slack : Form := .var 11

def sigma : Form := 1 - g - r
def tau : Form := s - 2 • g - 3 • r - ((9 : ℚ) / 10) • tail
def D : Form := 1 + s - 3 • g - 4 • r - tail + i
def j : Form := D - m - n
def a : Form := sigma - n
def b : Form := sigma - m
def Z : Form := z + x
def y : Form := j - x
def C : Form := sigma - Z
def u : Form := j + tail / 10 - i - Z - E
def splitBudget : Form := sigma / 2 + 2 • tau
def budget : Form := 2 • sigma + y - tau
def c : Form := C - w
def d : Form := a - E
def R : Form := b + r + z + i + E
def N : Form := 2 • r + y
def J : Form := C - d
def level : Form := R + w
def exceptional : Form := C + J + N - ((3 : ℚ) / 2) • R - 2 • w

inductive Band
  | completionLow | completionHigh | representedLow | representedMiddle | representedHigh
  deriving DecidableEq

def Band.represented : Band → Bool
  | .completionLow | .completionHigh => false
  | _ => true

def Band.lower : Band → ℚ
  | .completionLow | .representedLow => 1 / 10
  | .completionHigh | .representedMiddle => 1 / 7
  | .representedHigh => 1 / 4

def Band.upper : Band → ℚ
  | .completionLow | .representedLow => 1 / 7
  | .completionHigh | .representedMiddle => 1 / 4
  | .representedHigh => 1 / 3

/-- The three caps of Lemma 90(iii) and the two narrower caps in the following remark. -/
def Band.cap : Band → Form
  | .completionLow => .const (13 / 30) - ((47 : ℚ) / 30) • s
  | .completionHigh => .const (7 / 30) - ((19 : ℚ) / 30) • s
  | .representedLow => .const (1 / 2) - ((7 : ℚ) / 4) • s
  | .representedMiddle => .const (1 / 4) - ((1 : ℚ) / 2) • s
  | .representedHigh => .const (1 / 2) - ((3 : ℚ) / 2) • s

/-- Common non-strict rows, followed by the three band and slack rows of Lemma 90(iii).
The row order is the order in the published multiplier data. -/
def domain (band : Band) : List Form :=
  [1, s, g, r, tail, i, z, x, E, m, n, w, slack,
    tau, 3 • g + 4 • r - i, m - n, 2 • n - j, y, Z - E, a - E, C - w,
    .const (1 / 2) - w, sigma / 2 + tau - m, u] ++
  (if band.represented then [J] else []) ++
  [s - .const band.lower, .const band.upper - s - slack, band.cap - w - slack]

/-- The two possible failures of the split into the two largest and the two smallest
dual degrees, as listed in Lemma 90 equation (60). -/
def pairOptions : List Form := [2 • tau - j, splitBudget - m - n]

/-- The three possible failures of the split with the largest degree alone, equation (60). -/
def singleOptions : List Form :=
  [2 • tau - m, 2 • tau - (D - m), splitBudget - (D - m)]

def splitOptions (band : Band) : List (List Form) :=
  (pairOptions.flatMap fun p => singleOptions.map fun q => [p, q]) ++
  (if band = .representedHigh then [[4 • tau - sigma]] else [])

/-- The two possible reciprocal-completion failure rows, equation (60). -/
def reciprocalOptions : List Form := [u - C / 2, u + C / 2 - b]

/-- The seven possible direct failure rows before the gain, equation (60). -/
def directOptions : List Form :=
  [c + w + (R + w) + c, c + w + (R + w) + (R + d),
    c + w + N + c, c + w + N + (R + d),
    2 • c + d + w + (R + w + R) / 2, 2 • c + d + w + (N + R) / 2, 2 • d + N + R].map
      (fun k => y + b + w - z + k - 2 • budget)

/-- One of the eight choices in the positive parts of twice the level bound, equation (59). -/
def levelRow (useJ useN useExceptional : Bool) : Form :=
  2 • d + R + 2 • b + 2 • w + J + y - 2 • budget +
  (if useJ then J - level else 0) +
  (if useN then N - level else 0) +
  (if useExceptional then ((7 : ℚ) / 16) • exceptional else 0)

def levelOptions : List Form :=
  [false, true].flatMap fun useJ =>
    [false, true].flatMap fun useN =>
      [false, true].map fun useExceptional => levelRow useJ useN useExceptional

/-- Enumerate the Cartesian product of the selected failure rows. For the narrower
fallback caps the direct gain and represented-level bound are unnecessary. -/
def systems (band : Band) : List (List Form) :=
  (splitOptions band).flatMap fun split =>
    reciprocalOptions.flatMap fun reciprocal =>
      directOptions.flatMap fun direct =>
        if band.represented then
          levelOptions.map fun represented =>
            domain band ++ split ++ [reciprocal, direct, direct - E + z, represented]
        else [domain band ++ split ++ [reciprocal, direct]]

end ZetaSixth.Exponents.CertificateSystems
