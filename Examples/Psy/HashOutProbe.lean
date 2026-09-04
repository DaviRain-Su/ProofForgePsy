import ProofForge

namespace Examples.Psy.HashOutProbe

structure State where
  last0 : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { last0 := 0 }

@[pf_entry]
def getLast0 (s : State) : UInt64 :=
  s.last0

/-- Full HashOut Array4 product ABI: `Array UInt64 4` return aggregates 4
    limb calls; HashOut CSE dedups them to one circuit op. -/
@[pf_entry]
def hashPairFull (s : State) (a b : UInt64) : Except Error (State × UInt64 × UInt64 × UInt64 × UInt64) :=
  let l0 := ProofForge.Psy.Runtime.hashNoPadFull #[a, b] 0
  let l1 := ProofForge.Psy.Runtime.hashNoPadFull #[a, b] 1
  let l2 := ProofForge.Psy.Runtime.hashNoPadFull #[a, b] 2
  let l3 := ProofForge.Psy.Runtime.hashNoPadFull #[a, b] 3
  .ok ({ s with last0 := l0 }, l0, l1, l2, l3)

@[pf_entry]
def hashCombineFull (s : State)
    (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Except Error (State × UInt64 × UInt64 × UInt64 × UInt64) :=
  let l0 := ProofForge.Psy.Runtime.hashTwoToOneFull #[a0, a1, a2, a3, b0, b1, b2, b3] 0
  let l1 := ProofForge.Psy.Runtime.hashTwoToOneFull #[a0, a1, a2, a3, b0, b1, b2, b3] 1
  let l2 := ProofForge.Psy.Runtime.hashTwoToOneFull #[a0, a1, a2, a3, b0, b1, b2, b3] 2
  let l3 := ProofForge.Psy.Runtime.hashTwoToOneFull #[a0, a1, a2, a3, b0, b1, b2, b3] 3
  .ok ({ s with last0 := l0 }, l0, l1, l2, l3)

end Examples.Psy.HashOutProbe

#pf_psy_dump Examples.Psy.HashOutProbe
