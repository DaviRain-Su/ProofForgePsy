import ProofForge
import Lean
open Lean

namespace Examples.Psy.LoopProbe

structure State where
  total : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (initial : UInt64) : State :=
  { total := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.total

/-- Bounded for static-unroll probe: adds 1 four times. -/
@[pf_entry]
def run (s : State) (n : UInt64) : Except Error (State × UInt64) :=
  if n ≤ u64Max - 4 then
    let t := Id.run do
      let mut acc := s.total
      for _ in [0:4] do
        acc := acc + 1
      pure acc
    .ok ({ total := t }, t)
  else
    .error .overflow

/-- Checked arithmetic inside the loop body: adds 1, 2, 3, 4 over four steps. -/
@[pf_entry]
def scale (s : State) : Except Error (State × UInt64) :=
  let t1 := Id.run do
    let mut acc := s.total
    for _ in [0:4] do
      acc := acc + 1
    pure acc
  if t1 ≥ s.total then
    .ok ({ total := t1 }, t1)
  else
    .error .overflow

/-- Loop variable in the addend: sums 0+1+2+3 = 6 into total. -/
@[pf_entry]
def sumIx (s : State) : Except Error (State × UInt64) :=
  let t := Id.run do
    let mut acc := s.total
    for i in [0:4] do
      acc := acc + i.toUInt64
    pure acc
  if t ≥ s.total then
    .ok ({ total := t }, t)
  else
    .error .overflow

end Examples.Psy.LoopProbe

#pf_psy_dump Examples.Psy.LoopProbe
