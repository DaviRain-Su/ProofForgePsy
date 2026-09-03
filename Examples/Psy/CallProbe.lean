import ProofForge

namespace Examples.Psy.CallProbe

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

/-- Void sync external call probe: hashed static QN, no response binding. -/
@[pf_entry]
def notify (s : State) (x : UInt64) : Except Error (State × UInt64) :=
  if x ≤ u64Max - s.n then
    let _ := ProofForge.Psy.Runtime.psyVoidCall "Other.ping" #[x]
    let next := s.n + x
    .ok ({ n := next }, next)
  else
    .error .overflow

end Examples.Psy.CallProbe

#pf_psy_dump Examples.Psy.CallProbe