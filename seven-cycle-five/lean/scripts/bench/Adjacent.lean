import SevenCycle.Adjacent.FrontSearch

/-! Run with the compiled SevenCycleRuntime library. The input file contains
consecutive triples of little-endian UInt64 prefix masks. Passing "1111"
selects that profile; "all" includes all ordered transverse gap triples. -/

open SevenCycle SevenCycle.Adjacent

private def read64 (buf : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [:8] do
    v := v ||| (buf[off+i]!.toUInt64 <<< (8*i).toUInt64)
  return v

private def readHints (b : ByteArray) : Std.HashSet BandJoin.Prefix := Id.run do
  let mut out := {}
  for i in [:b.size/24] do
    let k := 24*i
    out := out.insert ⟨read64 b k, read64 b (k+8), read64 b (k+16)⟩
  return out

def main (args : List String) : IO UInt32 := do
  let [file,profile,first,last] := args | throw (IO.userError "expected HINTS.bin PROFILE FIRST LAST")
  let some lo := first.toNat? | throw (IO.userError "invalid first class")
  let some hi := last.toNat? | throw (IO.userError "invalid last class")
  unless lo < hi && hi ≤ atlasPlanes.size do throw (IO.userError "invalid target interval")
  unless profile == "1111" || profile == "all" do throw (IO.userError "expected profile 1111 or all")
  let bytes ← IO.FS.readBinFile file
  unless bytes.size % 24 == 0 do throw (IO.userError "incomplete prefix row")
  let start ← IO.monoMsNow
  let hints := readHints bytes
  let needed := hints.contains
  let idx := BandJoin.indexPrefixes Bitsets.orbitImages needed atlasPlanes
  IO.println s!"prefix_buckets={idx.size}"
  let dispatch : Scan.Visit := fun s t g cs v =>
    (profile == "all" || g == #v[1,1,1]) && BandStage.survives needed idx s t g cs v
  let ok := ScanFused.checkClasses (atlasPlanes.extract lo hi) dispatch SlabTables.leaf
  IO.println s!"profile={profile} classes=[{lo},{hi}) hints={hints.size} passed={ok}"
  let stop ← IO.monoMsNow
  IO.println s!"elapsed_ms={stop-start}"
  return if ok then 0 else 1
