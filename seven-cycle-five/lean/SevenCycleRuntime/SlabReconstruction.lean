import SevenCycleRuntime.Frames
import SevenCycleRuntime.Middle

namespace SevenCycle.Adjacent.SlabReconstruction
open SlabJoin Middle

abbrev Centers := Vector (Fin 7) 3

@[inline] def sourceSite (cs : Centers) (j : Nat) : Site :=
  ⟨Fin.ofNat 7 (coords j 1) + cs.get 0, Fin.ofNat 7 (coords j 2) + cs.get 1,
    Fin.ofNat 7 (coords j 3) + cs.get 2⟩

@[inline] def occupiedAt (s t u : Contacts.Cube) (cs : Centers) (j : Nat) : Bool :=
  let h := coords j 0
  let v := sourceSite cs j
  if h == 6 then occupied s v && !occupied u v
  else if h == 0 then occupied u v
  else if h == 1 then occupied t v && !occupied u v else false

def centeredMask (s t u : Contacts.Cube) (cs : Centers) : Nat :=
  maskUpTo (occupiedAt s t u cs) 2401

def rowIndex (rows : Array String) : Std.HashSet FrameMask :=
  let base := oneBitMap identityOrder 0
  Std.HashSet.ofArray (rows.map fun row => FrameMask.mk (movedMask base (readSlab row)))

def recorded (idx : Std.HashSet FrameMask) (s t : Contacts.Cube) (cs : Centers)
    (u : Contacts.Cube) : Bool :=
  idx.contains ⟨centeredMask s t u cs⟩

end SevenCycle.Adjacent.SlabReconstruction
