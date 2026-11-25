import SevenCycleRuntime.TypeThree

open SevenCycle.TypeThree

namespace SigTest

@[inline] def marker (x : UInt64) : UInt64 := (1 : UInt64) <<< ((x * 11400714819323198485) >>> 58)

structure Signature where
  b0 : UInt64
  b3 : UInt64
  c0 : UInt64
  c3 : UInt64
  deriving Inhabited

@[inline] def add (g : Signature) (r : CutRow) : Signature :=
  ⟨g.b0 ||| marker r.b0, g.b3 ||| marker r.b3,
   g.c0 ||| marker r.c0, g.c3 ||| marker r.c3⟩

def sig (rows : Array CutRow) : Signature := rows.foldl add ⟨0, 0, 0, 0⟩

@[inline] def share (x y : UInt64) : Bool := x &&& y != 0

def check (a a' b b' c c' : Signature) : Bool :=
  share a.b0 b.b0 && share a'.b0 b.b3 && share a.b3 b'.b0 && share a'.b3 b'.b3 &&
  share a.c0 c.b0 && share a'.c0 c.b3 && share b.c0 c.c0 && share b'.c0 c.c3 &&
  share a.c3 c'.b0 && share a'.c3 c'.b3 && share b.c3 c'.c0 && share b'.c3 c'.c3

def exact (a a' b b' c c' : Array CutRow) : Bool :=
  !check (sig a) (sig a') (sig b) (sig b') (sig c) (sig c') || rejectJoin a a' b b' c c'

def reject (g : SourceDomains) (t : CutRow) : Bool :=
  !g.b0.contains t.b0 || !g.b3.contains t.b3 || !g.c0.contains t.c0 || !g.c3.contains t.c3 ||
    exact (g.a0.getD t.a0 #[]) (g.a3.getD t.a3 #[]) (g.b0.getD t.b0 #[])
      (g.b3.getD t.b3 #[]) (g.c0.getD t.c0 #[]) (g.c3.getD t.c3 #[])

def rejectS (d q : Index) (i j : Fin 6) (s : CutRow) : Bool :=
  let allowed := d.getD (slot s j) {}
  let domains := sourceDomains d s
  (d.getD (slot s i) {}).all fun x _ => checkBuckets allowed (q.getD x {}) (reject domains)

def stage (reps : Array CutRow) (d q : Index) (i j : Fin 6) : Bool :=
  reps.all (rejectS d q i j)

end SigTest

namespace SigTest

def probing (g : SourceDomains) (t : CutRow) : Bool :=
  !g.b0.contains t.b0 || !g.b3.contains t.b3 || !g.c0.contains t.c0 || !g.c3.contains t.c3 ||
  !g.a0.contains t.a0 || !g.a3.contains t.a3 || t.a0 != (1:UInt64) <<< 63

def only (d q : Index) (i j : Fin 6) (s : CutRow) : Bool :=
  let allowed := d.getD (slot s j) {}
  let domains := sourceDomains d s
  (d.getD (slot s i) {}).all fun x _ => checkBuckets allowed (q.getD x {}) (probing domains)

def onlyStage (reps : Array CutRow) (d q : Index) (i j : Fin 6) : Bool :=
  reps.all (only d q i j)

end SigTest

namespace SigTest

abbrev B := Std.HashMap UInt64 Signature
abbrev D := Std.HashMap UInt64 B

def prep (d : Index) : D := d.map fun _ g => g.map fun _ rs => sig rs

structure Domains where
  a0 : B
  a3 : B
  b0 : B
  b3 : B
  c0 : B
  c3 : B

def sigRow (d : D) (s : CutRow) : Domains :=
  ⟨d.getD s.a0 {}, d.getD s.a3 {}, d.getD s.b0 {}, d.getD s.b3 {}, d.getD s.c0 {}, d.getD s.c3 {}⟩

@[inline] def vote (left : Signature) (r : B) (key : UInt64) : Bool :=
  share left.b0 ((r.getD key default).b0)

def pre (ss : Domains) (gs : SourceDomains) (t : CutRow) : Bool :=
  let a := ss.a0.getD t.a0 default
  !vote a ss.b0 t.b0 ||
    let b := ss.b0.getD t.b0 default
    let a' := ss.a3.getD t.a3 default
    !share a'.b0 b.b3 ||
      let b' := ss.b3.getD t.b3 default
      !share a.b3 b'.b0 || !share a'.b3 b'.b3 ||
        !check a a' b b' (ss.c0.getD t.c0 default) (ss.c3.getD t.c3 default) || rejectsPair gs t

def preS (d q : Index) (ds : D) (i j : Fin 6) (s : CutRow) : Bool :=
  let allowed := d.getD (slot s j) {}
  let domains := sourceDomains d s
  let marks := sigRow ds s
  (d.getD (slot s i) {}).all fun x _ => checkBuckets allowed (q.getD x {}) (pre marks domains)

def preStage (reps : Array CutRow) (d q : Index) (ds : D) (i j : Fin 6) : Bool :=
  reps.all (preS d q ds i j)

end SigTest
