import ProofForge

namespace Examples.Psy.WideProbe

open ProofForge.Core.Value

structure State where
  v : UInt128
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (a b : UInt64) : State :=
  { v := { w0 := a, w1 := b } }

@[pf_entry]
def getW0 (s : State) : UInt64 :=
  s.v.w0

@[pf_entry]
def getW1 (s : State) : UInt64 :=
  s.v.w1

/-- mutating: no-op ok (state unchanged). -/
@[pf_entry]
def noop (s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok (s, 0)
  else
    .error .overflow

end Examples.Psy.WideProbe

#pf_psy_dump Examples.Psy.WideProbe