import ProofForge

namespace Examples.Psy.BVecStateProbe

open ProofForge.Core.Value

structure State where
  vec : BoundedVec UInt64 2

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (a b : UInt64) : State :=
  { vec := { length := 2, values := #v[a, b] } }

@[pf_entry]
def initConst : State :=
  { vec := { length := 2, values := #v[7, 9] } }

@[pf_entry]
def getLen (s : State) : UInt64 :=
  s.vec.length.toUInt64

@[pf_entry]
def getFirst (s : State) : UInt64 :=
  s.vec.values.toArray[0]!

/-- mutating: no-op ok (state unchanged). -/
@[pf_entry]
def noop (s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok (s, 0)
  else
    .error .overflow

end Examples.Psy.BVecStateProbe

#pf_psy_dump Examples.Psy.BVecStateProbe
