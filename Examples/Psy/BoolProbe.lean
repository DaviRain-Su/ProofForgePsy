import ProofForge

namespace Examples.Psy.BoolProbe

structure State where
  f : Bool
  n : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (v : UInt64) : State := { f := true, n := v }

@[pf_entry]
def getN (s : State) : UInt64 := s.n

/-- Logical AND across Bool state and a scalar guard. -/
@[pf_entry]
def andProbe (s : State) (d : UInt64) : Except Error (State × UInt64) :=
  if s.f && d ≤ u64Max - s.n then
    let next := s.n + d
    .ok ({ s with n := next }, next)
  else
    .error .overflow

/-- Logical OR/NOT: flips the flag when the guard is active. -/
@[pf_entry]
def orProbe (s : State) (d : UInt64) : Except Error (State × UInt64) :=
  if !s.f || d ≤ u64Max - s.n then
    .ok ({ s with f := !s.f }, s.n)
  else
    .error .overflow

end Examples.Psy.BoolProbe

#pf_psy_dump Examples.Psy.BoolProbe
