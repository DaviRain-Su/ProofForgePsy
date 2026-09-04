import ProofForge

namespace Examples.Psy.ErrorProbe

structure State where
  level : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Named zero-arg errors: PSY-TYPED-ERROR tags the constructor name in the
    DPN assert record; structured payloads stay fail-closed. -/
inductive Error where
  | overflow
  | tooHigh
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (v : UInt64) : State :=
  { level := v }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.level

@[pf_entry]
def raise (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if delta ≤ 255 then
    if s.level ≤ u64Max - delta then
      let next := s.level + delta
      .ok ({ level := next }, next)
    else
      .error .tooHigh
  else
    .error .overflow

end Examples.Psy.ErrorProbe

#pf_psy_dump Examples.Psy.ErrorProbe