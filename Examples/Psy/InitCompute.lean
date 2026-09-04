import ProofForge

namespace Examples.Psy.InitCompute

structure State where
  scaled : UInt64
  offset : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- init with computation: locals bind intermediate values before stores. -/
@[pf_entry]
def init (base factor : UInt64) : State :=
  let scaled := base * factor
  let offset := base + factor
  { scaled := scaled, offset := offset }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.scaled

@[pf_entry]
def raiseLevel (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if delta ≤ u64Max - s.scaled then
    let next := s.scaled + delta
    .ok ({ scaled := next, offset := s.offset }, next)
  else
    .error .overflow

end Examples.Psy.InitCompute

#pf_psy_dump Examples.Psy.InitCompute