import ProofForge

namespace Examples.Psy.WideCounter

open ProofForge.Core.Value

structure State where
  v : UInt128
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Initialize both UInt128 limbs from two UInt64 params. -/
@[pf_entry]
def init (a b : UInt64) : State :=
  { v := { w0 := a, w1 := b } }

/-- Read low limb. -/
@[pf_entry]
def getW0 (s : State) : UInt64 :=
  s.v.w0

/-- Read high limb. -/
@[pf_entry]
def getW1 (s : State) : UInt64 :=
  s.v.w1

/-- Set both limbs from params (full constructor rebuild; source-level
    sibling-limb reads in a mutating update are a known extractor FC). -/
@[pf_entry]
def setBoth (s : State) (a b : UInt64) : Except Error (State × UInt64) :=
  .ok ({ v := { w0 := a, w1 := b } }, a)

end Examples.Psy.WideCounter

#pf_psy_dump Examples.Psy.WideCounter
