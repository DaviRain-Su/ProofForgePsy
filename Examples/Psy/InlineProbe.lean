import ProofForge

namespace Examples.Psy.InlineProbe

structure State where
  n : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- `@[pf_inline]` helper: erased before Core ops reach targets (the
    extractor inlines it); kernel proofs still check it. -/
@[pf_inline]
def doubled (x : UInt64) : UInt64 := x + x

@[pf_entry]
def init (v : UInt64) : State := { n := v }

@[pf_entry]
def get (s : State) : UInt64 := s.n

@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if delta ≤ u64Max - s.n then
    let next := s.n + doubled delta
    .ok ({ n := next }, next)
  else
    .error .overflow

end Examples.Psy.InlineProbe