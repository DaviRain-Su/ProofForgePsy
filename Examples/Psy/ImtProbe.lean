import ProofForge

namespace Examples.Psy.ImtProbe

structure State where
  last : UInt64
  deriving Repr, DecidableEq, Inhabited

@[pf_entry]
def init : State :=
  { last := 0 }

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def peek (s : State) : UInt64 :=
  s.last

/-- IMT self-current pilot (expression-position `pf.imt.*`).
    UInt64 keys/values pack as [v, 0, 0, 0] limbs; base 0, capacity 2^20. -/
@[pf_entry]
def put (s : State) (k v : UInt64) : Except Error (State × UInt64) :=
  let w := ProofForge.Psy.Runtime.imtSet k v
  .ok ({ s with last := w }, w)

@[pf_entry]
def get (s : State) (k : UInt64) : Except Error (State × UInt64) :=
  let v := ProofForge.Psy.Runtime.imtGet k
  .ok ({ s with last := v }, v)

@[pf_entry]
def has (s : State) (k : UInt64) : Except Error (State × UInt64) :=
  let c := ProofForge.Psy.Runtime.imtContains k
  .ok ({ s with last := c }, c)

/-- External-contract IMT read (same user, other contract id). -/
@[pf_entry]
def getExt (s : State) (cid k : UInt64) : Except Error (State × UInt64) :=
  let v := ProofForge.Psy.Runtime.imtGetExternal cid k
  .ok ({ s with last := v }, v)

/-- Other-user IMT read / contains. -/
@[pf_entry]
def getOther (s : State) (uid cid k : UInt64) : Except Error (State × UInt64) :=
  let v := ProofForge.Psy.Runtime.imtGetOther uid cid k
  .ok ({ s with last := v }, v)

@[pf_entry]
def hasOther (s : State) (uid cid k : UInt64) : Except Error (State × UInt64) :=
  let c := ProofForge.Psy.Runtime.imtContainsOther uid cid k
  .ok ({ s with last := c }, c)

end Examples.Psy.ImtProbe

#pf_psy_dump Examples.Psy.ImtProbe