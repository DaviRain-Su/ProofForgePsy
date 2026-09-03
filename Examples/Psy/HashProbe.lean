import ProofForge

namespace Examples.Psy.HashProbe

structure State where
  h : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { h := 0 }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.h

/-- ADR-0039 crypto gadgets (expression-position `pf.crypto.*`):
    scalar product ABI = first HashOut limb. -/
@[pf_entry]
def hashPair (s : State) (a b : UInt64) : Except Error (State × UInt64) :=
  let x := ProofForge.Psy.Runtime.hashNoPad #[a, b]
  .ok ({ s with h := x }, x)

@[pf_entry]
def hashPadded (s : State) (a b : UInt64) : Except Error (State × UInt64) :=
  let x := ProofForge.Psy.Runtime.hashPad #[a, b]
  .ok ({ s with h := x }, x)

@[pf_entry]
def hashCombine (s : State)
    (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Except Error (State × UInt64) :=
  let x := ProofForge.Psy.Runtime.hashTwoToOne #[a0, a1, a2, a3, b0, b1, b2, b3]
  .ok ({ s with h := x }, x)

@[pf_entry]
def keccakWord (s : State) (w : UInt64) : Except Error (State × UInt64) :=
  let x := ProofForge.Psy.Runtime.keccak256 #[w]
  .ok ({ s with h := x }, x)

end Examples.Psy.HashProbe

#pf_psy_dump Examples.Psy.HashProbe