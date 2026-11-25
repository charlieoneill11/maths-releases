import SevenCycleRuntime.PrefixHintData

namespace SevenCycle.Adjacent.PrefixHint

/-- SplitMix64's finalizer, applied with wrapping 64-bit arithmetic. -/
@[inline] def mix (x : UInt64) : UInt64 :=
  let a := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let b := (a ^^^ (a >>> 27)) * 0x94d049bb133111eb
  b ^^^ (b >>> 31)

private def digit (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b - 65
  else if 97 ≤ b && b ≤ 122 then b - 97 + 26
  else if 48 ≤ b && b ≤ 57 then b - 48 + 52
  else if b == 45 then 62 else 63

/-- Each alphabet digit stores six consecutive bitmap bits, least significant
first. The final digit holds the last two bits of the 2²¹-bit table. -/
def bitmap : ByteArray :=
  PrefixHintData.chunks.foldl (init := ByteArray.empty) fun acc chunk =>
    chunk.toUTF8.foldl (fun a b => a.push (digit b)) acc

@[inline] def bit (i : UInt64) : Bool :=
  let pos := (i &&& 0x1fffff).toNat
  (bitmap[pos / 6]?.getD 0).toNat.testBit (pos % 6)

/-- An approximate membership test used to retain sparse six-band domains.
The band checker verifies the final continuation also for absent keys. -/
def containsTriple (first second middle : UInt64) : Bool :=
  let h := mix (mix ((first * 0x9e3779b97f4a7c15) ^^^ second) ^^^ middle)
  bit h && bit (h >>> 32)

end SevenCycle.Adjacent.PrefixHint
