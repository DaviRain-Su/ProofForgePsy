import ProofForge

namespace Examples.Psy.MultiRetProbe

structure State where
  a : UInt64
  b : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (v : UInt64) : State := { a := v, b := v }

@[pf_entry]
def getSum (s : State) : UInt64 := s.a + s.b

@[pf_entry]
def both (s : State) (d : UInt64) : Except Error (State × UInt64 × UInt64) :=
  if d ≤ u64Max - s.a then
    if d ≤ u64Max - s.b then
      .ok ({ a := s.a + d, b := s.b + d }, s.a + d, s.b + d)
    else
      .error .overflow
  else
    .error .overflow

end Examples.Psy.MultiRetProbe

#pf_psy_dump Examples.Psy.MultiRetProbe
