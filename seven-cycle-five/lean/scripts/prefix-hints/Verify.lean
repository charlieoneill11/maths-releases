import SevenCycle.Adjacent.PrefixHint

open SevenCycle.Adjacent

private def word (bs : ByteArray) (offset : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for j in [0:8] do
    w := w ||| ((bs[offset+j]!).toUInt64 <<< (8*j).toUInt64)
  return w

/-- Check the Lean decoder against every cut triple emitted by the release. -/
def main (paths : List String) : IO Unit := do
  let ref :: paths := paths | throw (IO.userError "pass the reference bitmap and extracted hints.bin files")
  if paths.isEmpty then throw (IO.userError "pass one or more extracted hints.bin files")
  let raw ← IO.FS.readBinFile ref
  if raw.size != 262144 then throw (IO.userError "invalid reference bytes")
  if PrefixHint.bitmap.size != 349526 then throw (IO.userError "invalid bitmap size")
  for i in [0:2097152] do
    if PrefixHint.bit i.toUInt64 != raw[i / 8]!.toNat.testBit (i % 8) then
      throw (IO.userError s!"reference mismatch at bit {i}")
  IO.println "2097152 bitmap positions verified"
  for path in paths do
    let bytes ← IO.FS.readBinFile path
    if bytes.isEmpty || bytes.size % 24 != 0 then throw (IO.userError s!"invalid records in {path}")
    for i in [0:bytes.size/24] do
      let off := 24*i
      let k : BandJoin.Prefix := ⟨word bytes off,word bytes (off+8),word bytes (off+16)⟩
      if !PrefixHint.needed k then throw (IO.userError s!"missing {path} key {i}")
    IO.println s!"{path} {bytes.size/24} keys"
