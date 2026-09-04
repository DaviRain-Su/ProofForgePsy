import ProofForge

namespace Examples.Psy.AggProbe

open ProofForge.Core.Value

structure State where
  a : UInt64
  b : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (v : UInt64) : State := { a := v, b := v }

@[pf_entry]
def getA (s : State) : UInt64 := s.a

/-- aggregate return: UInt64 scalar + Bool leaf (B-RET-AGG non-UInt64 leaf). -/
@[pf_entry]
def getBoth (s : State) : Except Error (State × UInt64 × Bool) :=
  .ok (s, s.a, true)

/-- BoundedVec fixed-capacity aggregate return (length + N×Felt leaves). -/
@[pf_entry]
def getPair (s : State) : Except Error (State × UInt64 × BoundedVec UInt64 2) :=
  .ok (s, 0, { length := 2, values := #v[s.a, s.b] })

end Examples.Psy.AggProbe

#pf_psy_dump Examples.Psy.AggProbe
