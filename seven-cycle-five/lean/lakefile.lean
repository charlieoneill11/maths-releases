import Lake

open System Lake DSL

package «seven-cycle» where version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "v4.29.1"

/-- Read a Linux memory statistic without requiring procfs on other hosts. -/
private def readLimit (path : FilePath) : IO (Option String) := do
  try return some (← IO.FS.readFile path).trimAscii.toString
  catch _ => return none

private def memoryField (stat field : String) : Option Nat := do
  let line ← (stat.splitOn "\n").find? (·.startsWith (field ++ " "))
  (line.splitOn " ").findSome? String.toNat?

private def proofWorkers : IO Nat := do
  if let some raw := ← IO.getEnv "SEVEN_CYCLE_JOBS" then
    match raw with
    | "1" => return 1
    | "2" => return 2
    | _ => throw (IO.userError "SEVEN_CYCLE_JOBS must be 1 or 2")
  let some mem ← readLimit "/proc/meminfo" | return 1
  let some kib := memoryField mem "MemAvailable:" | return 1
  let threshold : Nat := 12 * 1024 * 1024 * 1024
  if kib * 1024 < threshold then return 1
  let limits : List (FilePath × String × String × String) := [("/sys/fs/cgroup", "memory.max", "memory.current", "inactive_file"),
    ("/sys/fs/cgroup/memory", "memory.limit_in_bytes", "memory.usage_in_bytes", "total_inactive_file")]
  for (dir, maxFile, currentFile, inactive) in limits do
    if let some ceiling ← readLimit (dir / maxFile) then
      if let some bytes := ceiling.toNat? then
        let some current ← readLimit (dir / currentFile) | return 1
        let some used := current.toNat? | return 1
        let stats := (← readLimit (dir / "memory.stat")).getD ""
        let reclaimable := (memoryField stats inactive).getD 0
        if bytes - (used - reclaimable) < threshold then return 1
  return 2

/-- Build the ordinary Lean artifacts in dependency order. Lake's builtin
library builder submits the entire import graph at once, which can run dozens
of multi-gigabyte native proofs concurrently. Independent proof modules keep
their actual imports so they can also be checked on separate CI workers. -/
private def boundedModules (modules : Array Lake.Module) : FetchM (Job Unit) := do
  let limit ← proofWorkers
  let mut ordered := OrdModuleSet.empty
  for mod in modules do
    ordered := (ordered.appendArray (← (← mod.transImports.fetch).await)).insert mod
  let mut pending := Job.nil
  let mut count := 0
  for mod in ordered.toArray do
    if `SevenCycle.Native.Adjacent |>.isPrefixOf mod.name then
      -- These six-band searches hold both the contact index and the full band index.
      pending.await
      pending := Job.nil
      count := 0
      discard (← mod.leanArts.fetch).await
    else
      pending := pending.mix (← mod.leanArts.fetch)
      count := count + 1
      if count == limit then
        pending.await
        pending := Job.nil
        count := 0
  return pending

library_facet proofModules (lib : LeanLib) : Unit := do
  boundedModules (← (← lib.modules.fetch).await)

/-- CI workers certify disjoint portions of the same Native module set. Sorting
makes the partition independent of filesystem traversal order on each runner. -/
library_facet nativeLane (lib : LeanLib) : Unit := do
  let some lane := (← IO.getEnv "SEVEN_CYCLE_LANE").bind String.toNat? | error "set SEVEN_CYCLE_LANE"
  let some lanes := (← IO.getEnv "SEVEN_CYCLE_LANES").bind String.toNat? | error "set SEVEN_CYCLE_LANES"
  unless lane < lanes do error "the native lane must be below the number of lanes"
  let mods ← (← lib.modules.fetch).await
  let natives := (mods.filter (fun mod => (lib.name ++ `Native).isPrefixOf mod.name)).qsort
    (fun x y => x.name.toString < y.name.toString)
  let mut selected := #[]
  for (mod, i) in natives.zipIdx do
    if i % lanes == lane then
      selected := selected.push mod
  boundedModules selected

@[default_target]
lean_lib SevenCycle where
  globs := #[`SevenCycle, `SevenCycle.+]
  defaultFacets := #[LeanLib.facetKind ++ `proofModules]

lean_lib SevenCycleRuntime where
  roots := #[]
  globs :=
  #[`SevenCycleRuntime, `SevenCycleRuntime.Adaptive, `SevenCycleRuntime.Adjacent, `SevenCycleRuntime.Orbit,
    `SevenCycleRuntime.TypeThree]
  precompileModules := true

lean_lib SevenCycleAtlasRuntime where
  roots := #[]
  globs := #[`SevenCycleRuntime.AtlasPrune, `SevenCycleRuntime.PlaneSearch]
  precompileModules := true

lean_lib SevenCycleTwoRuntime where
  roots := #[]
  globs :=
  #[`SevenCycleRuntime.TypeTwo, `SevenCycleRuntime.TypeTwoCross, `SevenCycleRuntime.TypeTwoDomains,
    `SevenCycleRuntime.TypeTwoGraph, `SevenCycleRuntime.TypeTwoMatching, `SevenCycleRuntime.TypeTwoMiddle,
    `SevenCycleRuntime.TypeTwoSearch]
  precompileModules := true

lean_lib SevenCycleAdjacentRuntime where
  roots := #[]
  globs :=
  #[`SevenCycleRuntime.AdjacentBands, `SevenCycleRuntime.AdjacentDomains, `SevenCycleRuntime.AdjacentScan,
    `SevenCycleRuntime.BandCounts, `SevenCycleRuntime.BandStage, `SevenCycleRuntime.Contacts, `SevenCycleRuntime.Frames,
    `SevenCycleRuntime.FusedMiddle, `SevenCycleRuntime.Middle, `SevenCycleRuntime.MixedSlabs,
    `SevenCycleRuntime.SlabJoin, `SevenCycleRuntime.SlabReconstruction, `SevenCycleRuntime.SlabTables]
  precompileModules := true

lean_lib SevenCyclePrefixRuntime where
  roots := #[]
  globs := #[`SevenCycleRuntime.PrefixHint, `SevenCycleRuntime.PrefixHintData]
  precompileModules := true
