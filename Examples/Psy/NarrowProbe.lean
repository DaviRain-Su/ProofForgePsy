import ProofForge

namespace Examples.Psy.NarrowProbe

structure State where
  small : UInt8
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (v : UInt8) : State :=
  { small := v }

@[pf_entry]
def getSmall (s : State) : UInt8 :=
  s.small

/-- checked add: v + s.small, guard traps on UInt8 overflow (≤ 255). -/
@[pf_entry]
def addSmall (s : State) (v : UInt8) : Except Error (State × UInt8) :=
  if v ≤ ~~~(0 : UInt8) - s.small then
    .ok ({ small := v + s.small }, v + s.small)
  else
    .error .overflow

/-- checked sub: s.small - v, guard traps on UInt8 underflow. -/
@[pf_entry]
def subSmall (s : State) (v : UInt8) : Except Error (State × UInt8) :=
  if s.small ≥ v then
    .ok ({ small := s.small - v }, s.small - v)
  else
    .error .overflow

end Examples.Psy.NarrowProbe

#pf_psy_dump Examples.Psy.NarrowProbe
