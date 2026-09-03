import ProofForge

namespace Examples.Psy.EventProbe

structure State where
  n : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (v : UInt64) : State :=
  { n := v }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.n

/-- DPN event probe: emit a `Ping` record then update state. -/
@[pf_entry]
def ping (s : State) (x : UInt64) : Except Error (State × UInt64) :=
  if x ≤ u64Max - s.n then
    let next := s.n + x
    let _ := ProofForge.Psy.Runtime.psyEvent "Ping" x
    .ok ({ n := next }, next)
  else
    .error .overflow

end Examples.Psy.EventProbe

#pf_psy_dump Examples.Psy.EventProbe