import ProofForge

namespace Examples.Psy.OptionProbe

/-- Option UInt64 state (slot_tag + slot_p0 two-leaf layout, OptionState
    shape from the official matrix). -/
structure State where
  slot : Option UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def initSome (v : UInt64) : State :=
  { slot := some v }

@[pf_entry]
def initNone : State :=
  { slot := none }

@[pf_entry]
def peek (s : State) : UInt64 :=
  match s.slot with
  | some v => v
  | none => 0

/-- setSome: overwrite the payload and tag. -/
@[pf_entry]
def setSome (s : State) (v : UInt64) : Except Error (State × UInt64) :=
  .ok ({ s with slot := some v }, v)

/-- clear: tag → none-payload. -/
@[pf_entry]
def clear (s : State) : Except Error (State × UInt64) :=
  .ok ({ s with slot := none }, 0)

end Examples.Psy.OptionProbe

#pf_psy_dump Examples.Psy.OptionProbe
