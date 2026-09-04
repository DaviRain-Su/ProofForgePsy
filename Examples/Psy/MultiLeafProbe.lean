import ProofForge

namespace Examples.Psy.MultiLeafProbe

structure State where
  a : UInt64
  b : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (v : UInt64) : State :=
  { a := v, b := v }

@[pf_entry]
def getSum (s : State) : UInt64 :=
  s.a + s.b

/-- Atomic multi-leaf update: the extractor snapshots both reads before
    either store (storeAggregate semantics; swap-proof). -/
@[pf_entry]
def swapAdd (s : State) (d : UInt64) : Except Error (State × UInt64) :=
  if d ≤ u64Max - s.a then
    if d ≤ u64Max - s.b then
      let a' := s.a + d
      let b' := s.b + d
      .ok ({ a := a', b := b' }, a')
    else
      .error .overflow
  else
    .error .overflow

/-- Cross-referencing stores: `a := b; b := a` must swap against the OLD
    state (snapshot prevents store-then-read hazards). -/
@[pf_entry]
def cross (s : State) : Except Error (State × UInt64) :=
  .ok ({ a := s.b, b := s.a }, s.b)

end Examples.Psy.MultiLeafProbe

#pf_psy_dump Examples.Psy.MultiLeafProbe