import G3Sig
import SevenCycleRuntime.Adaptive
import SevenCycle.Bitsets.Orbit
import SevenCycle.AtlasData
open SevenCycle SevenCycle.Bitsets SevenCycle.TypeThree

@[noinline] def useN (x tick : Nat) := if tick < 2^128 then x else x + 1

def note (s : String) : IO Unit := do
  let f ← IO.getStdout
  f.putStrLn s
  f.flush

def cpu : IO Nat := do
  let fields := (← IO.FS.readFile "/proc/self/stat").splitOn " "
  return fields[13]!.toNat! + fields[14]!.toNat!

def main (args : List String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let n := useN args[0]!.toNat! t0
  let m := args[1]!.toNat!
  let reps := (Array.range m).map fun i => atlasPlanes[i*1016/m]!
  let sources := packRows reps translationImages
  let rows := packRows (atlasPlanes.extract 0 n) orbitImages
  note s!"rows={rows.size} sources={sources.size} last={(rows[rows.size-1]!).c3}"
  let t1 ← IO.monoMsNow
  let d := makeIndex CutRow.a0 CutRow.a3 rows
  note s!"masks={d.size}"
  let t2 ← IO.monoMsNow
  let freq := estimateSlots d rows
  let group := sources.filter fun r => leastSlots freq r == (0,1)
  note s!"group={group.size}"
  let t3 ← IO.monoMsNow
  let ds := SigTest.prep d
  note s!"summary={ds.size}"
  let tx ← IO.monoMsNow
  let start ← cpu
  let only := SigTest.onlyStage group d d 0 1
  note s!"only={only}"
  let tests ← cpu
  let h := SigTest.preStage group d d ds 0 1
  note s!"outcome={h}"
  let marks ← cpu
  let native := group.all (rejectsSource d d 0 1)
  note s!"direct={native}"
  let exact ← cpu
  note s!"CPU centiseconds six={tests-start} cached={marks-tests} direct={exact-marks}"
  let t4 ← IO.monoMsNow
  note s!"n={n} m={m} gen={t1-t0} index={t2-t1} select={t3-t2} scan={t4-tx} prep={tx-t3}ms"
