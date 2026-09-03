/-
  Psy Plan → canonical DPN package (psy-dpn-v1 slice).

  Ported from `ProofForgeV2.Targets.Psy.Dpn.LowerPlanV1`, reduced to the
  constructors this repository's `Psy.Plan` can express:

  * Counter-shaped templates (init store / checkedAdd store+return / view
    load) pinned to the golden package shape.
  * General builder: params/prelude, multi-leaf state loads/stores with
    Constant leaf wires, checked UInt64 arithmetic with trap assertions,
    comparisons, bool logic, Select mux, conditional stores under a write
    condition, context reads, if/else with Select-merged returns.
  * Not ported (no Plan constructor produces them): forLoop unroll,
    switchOn, events, external calls, IMT, hash gadgets, wide bindings,
    narrow/signed lanes, pureHelper inlining, storeAggregate/returnAggregate.

  Method ids: canonical `genDapenContractFunctionMethodId` SHA-256 algorithm
  (`p{sourceIndex}` size-1 args); Counter pins remain as regression goldens.
-/
import ProofForge.Psy.Plan
import ProofForge.Psy.Dpn.Schema
import ProofForge.Crypto.Sha256

namespace ProofForge.Psy.Dpn.Lower

open ProofForge.Psy.Plan
open ProofForge.Psy.Dpn.Schema

private def planError (message : String) : Except String α :=
  .error s!"psy/dpn: {message}"

/-- Pinned Counter method ids. Regression pins only — the product path uses
    `genDapenContractFunctionMethodIdV1`. -/
def pinnedMethodIdV1 (name : String) : Option UInt32 :=
  match name with
  | "initialize" => some 202172507
  | "increment" => some 1990357658
  | "get" => some 1459926901
  | _ => none

/-- Official `psy_crypto::hash::utils::gen_dapen_contract_function_method_id`.

    preimage = `method_name` + `(` + join(`arg_name` + `[` + `size` + `]`, `,`) + `)`
    method_id = first 4 LE bytes of SHA-256(UTF-8 preimage) as `u32`. -/
def genDapenContractFunctionMethodIdV1
    (methodName : String) (args : Array (String × Nat)) : UInt32 :=
  let argPortion :=
    String.intercalate ","
      (args.map (fun (n, sz) => s!"{n}[{sz}]")).toList
  let preimage := s!"{methodName}({argPortion})"
  let dig := ProofForge.Crypto.Sha256.digestBytes preimage
  let b0 := dig[0]!.toUInt32
  let b1 := dig[1]!.toUInt32
  let b2 := dig[2]!.toUInt32
  let b3 := dig[3]!.toUInt32
  b0 ||| UInt32.shiftLeft b1 8 ||| UInt32.shiftLeft b2 16 |||
    UInt32.shiftLeft b3 24

/-- Each physical PlanParam becomes `p{sourceIndex}` with Felt size 1.
    Bool / UInt leaves are each one circuit input. -/
def methodIdArgsFromPlanParamsV1 (params : Array PlanParam) : Array (String × Nat) :=
  params.map fun p => (s!"p{p.sourceIndex}", 1)

/-- Product method_id from method name plus canonical `(name, size)` args. -/
def requireMethodIdV1 (name : String) (args : Array (String × Nat)) :
    Except String UInt32 :=
  pure (genDapenContractFunctionMethodIdV1 name args)

/-- Product method_id from a PlanFunction (caller package method name + p0.. args). -/
def requireMethodIdFromPlanFnV1 (fn : PlanFunction) : Except String UInt32 :=
  requireMethodIdV1 fn.name (methodIdArgsFromPlanParamsV1 fn.params)

private def bTrue : UInt64 := encodeIndexedId .bool 0

/-- Max physical state leaves admitted by this slice. -/
def maxStateLeavesV1 : Nat := 64

/-- View get: Constant + GetState(sub_slot 0) → output target 1. -/
def lowerViewLoadReturnV1 (name : String) (fieldIndex : Nat) :
    Except String FunctionCircuitDefV1 := do
  unless fieldIndex == 0 do
    planError "only state field 0 supported in Counter/view template"
  let methodId ← requireMethodIdV1 name #[]
  pure {
    name, methodId
    circuitInputs := #[]
    circuitOutputs := #[1]
    stateCommands := #[.getSelfUserCurrentContractStateSlotSingle 0]
    stateCommandResolutionIndices := #[1]
    assertions := #[]
    definitions := #[
      { dataType := .target, index := 0, opType := .constant, inputs := #[0] },
      { dataType := .target, index := 1, opType := .getStateCommandResultSingle, inputs := #[0] }
    ]
    events := #[]
  }

/-- initialize: store param 0 into field 0 (canonical sub-slot 1). -/
def lowerInitializeStoreParamV1 (name : String) (fieldIndex : Nat) :
    Except String FunctionCircuitDefV1 := do
  unless fieldIndex == 0 do
    planError "only state field 0 supported in Counter/init template"
  let methodId ← requireMethodIdV1 name #[("p0", 1)]
  pure {
    name, methodId
    circuitInputs := #[0]
    circuitOutputs := #[]
    stateCommands := #[
      .getSelfUserCurrentContractStateSlotSingle 1,
      .setContractStateSlotSingle bTrue 1 0
    ]
    stateCommandResolutionIndices := #[2, 3]
    assertions := #[]
    definitions := #[
      { dataType := .target, index := 0, opType := .inputTarget, inputs := #[0] },
      { dataType := .target, index := 1, opType := .constant, inputs := #[0] },
      { dataType := .bool, index := 0, opType := .constantTrue, inputs := #[1] }
    ]
    events := #[]
  }

/-- increment-shaped: store(checkedAdd(load,param)); return load. -/
def lowerCheckedAddStoreReturnV1 (name : String) (fieldIndex : Nat) :
    Except String FunctionCircuitDefV1 := do
  unless fieldIndex == 0 do
    planError "only state field 0 supported in Counter/mutate template"
  let methodId ← requireMethodIdV1 name #[("p0", 1)]
  pure {
    name, methodId
    circuitInputs := #[0]
    circuitOutputs := #[4]
    stateCommands := #[
      .getSelfUserCurrentContractStateSlotSingle 1,
      .setContractStateSlotSingle bTrue 1 3,
      .getSelfUserCurrentContractStateSlotSingle 1
    ]
    stateCommandResolutionIndices := #[2, 5, 5]
    assertions := #[{
      left := encodeIndexedId .bool 1
      right := encodeIndexedId .bool 0
      message := "u64 add overflow"
    }]
    definitions := #[
      { dataType := .target, index := 0, opType := .inputTarget, inputs := #[0] },
      { dataType := .target, index := 1, opType := .constant, inputs := #[0] },
      { dataType := .bool, index := 0, opType := .constantTrue, inputs := #[1] },
      { dataType := .target, index := 2, opType := .getStateCommandResultSingle, inputs := #[0] },
      { dataType := .target, index := 3, opType := .add, inputs := #[2, 0] },
      { dataType := .bool, index := 1, opType := .gte, inputs := #[3, 2] },
      { dataType := .target, index := 4, opType := .getStateCommandResultSingle, inputs := #[2] }
    ]
    events := #[]
  }

/-! ## General builder -/

/-- Circuit wire: target (Felt/UInt64), bool, or u32Target, per-type index. -/
inductive WireV1 where
  | target (index : Nat)
  | bool (index : Nat)
  | u32 (index : Nat)
  deriving BEq, Inhabited, Repr

def WireV1.encoded : WireV1 → UInt64
  | .target i => encodeIndexedId .target i
  | .bool i => encodeIndexedId .bool i
  | .u32 i => encodeIndexedId .u32Target i

def WireV1.rawIndex : WireV1 → Nat
  | .target i => i
  | .bool i => i
  | .u32 i => i

/-- Operand id for DPN ops: Target→raw index, Bool/U32→encoded. -/
def WireV1.operand : WireV1 → UInt64
  | w => w.encoded

structure BuilderV1 where
  nextTarget : Nat := 0
  nextBool : Nat := 0
  nextU32 : Nat := 0
  defs : Array IndexedVarDefV1 := #[]
  cmds : Array StateCmdV1 := #[]
  res : Array Nat := #[]
  asserts : Array AssertEqV1 := #[]
  /-- Shared Constant 0 target index (always allocated at start of general lower). -/
  zeroTarget : Nat := 0
  /-- Shared ConstantTrue bool index. -/
  trueBool : Nat := 0
  /-- Optional ConstantFalse. -/
  falseBool? : Option Nat := none
  /-- True when the Plan has >1 physical state leaf (multi-leaf map). -/
  multiLeaf : Bool := false
  deriving Inhabited

private def pushTarget (b : BuilderV1) (op : OpTypeV1) (inputs : Array UInt64) :
    BuilderV1 × WireV1 :=
  let idx := b.nextTarget
  let defn : IndexedVarDefV1 := {
    dataType := .target, index := idx, opType := op, inputs
  }
  ({ b with
      nextTarget := idx + 1
      defs := b.defs.push defn }, .target idx)

private def pushBool (b : BuilderV1) (op : OpTypeV1) (inputs : Array UInt64) :
    BuilderV1 × WireV1 :=
  let idx := b.nextBool
  let defn : IndexedVarDefV1 := {
    dataType := .bool, index := idx, opType := op, inputs
  }
  ({ b with
      nextBool := idx + 1
      defs := b.defs.push defn }, .bool idx)

private def pushU32 (b : BuilderV1) (op : OpTypeV1) (inputs : Array UInt64) :
    BuilderV1 × WireV1 :=
  let idx := b.nextU32
  let defn : IndexedVarDefV1 := {
    dataType := .u32Target, index := idx, opType := op, inputs
  }
  ({ b with
      nextU32 := idx + 1
      defs := b.defs.push defn }, .u32 idx)

/-- Allocate InputTarget wires for each param (index 0..n-1). -/
private def emitParams (n : Nat) : BuilderV1 × Array WireV1 := Id.run do
  let mut b : BuilderV1 := {}
  let mut wires : Array WireV1 := #[]
  for i in [0:n] do
    let (b', w) := pushTarget b .inputTarget #[UInt64.ofNat i]
    b := b'
    wires := wires.push w
  pure (b, wires)

/-- Ensure zero + ConstantTrue exist (after params). -/
private def ensurePrelude (b : BuilderV1) : BuilderV1 :=
  if b.defs.isEmpty && b.nextTarget == 0 then
    -- no params path: const 0 then true
    let (b1, z) := pushTarget b .constant #[0]
    let (b2, _) := pushBool b1 .constantTrue #[UInt64.ofNat z.rawIndex]
    { b2 with zeroTarget := z.rawIndex, trueBool := 0 }
  else
    -- params already emitted; add const 0 + true
    let (b1, z) := pushTarget b .constant #[0]
    let (b2, t) := pushBool b1 .constantTrue #[UInt64.ofNat z.rawIndex]
    { b2 with zeroTarget := z.rawIndex, trueBool := t.rawIndex }

private def ensureFalse (b : BuilderV1) : BuilderV1 × WireV1 :=
  match b.falseBool? with
  | some i => (b, .bool i)
  | none =>
      let (b', w) := pushBool b .constantFalse #[UInt64.ofNat b.zeroTarget]
      ({ b' with falseBool? := some w.rawIndex }, w)

private def trueWire (b : BuilderV1) : WireV1 := .bool b.trueBool

private def zeroWire (b : BuilderV1) : WireV1 := .target b.zeroTarget

/-- Physical storage leaf index for a Plan field. This slice keeps contiguous
    leaves 0..n-1 in declaration order on both single- and multi-leaf paths. -/
private def physicalLeafIndex (_b : BuilderV1) (fieldIndex : Nat) : Nat :=
  fieldIndex

/-- Emit (or reuse zero) a Target Constant equal to `leaf`, returning the
    bare target index to place in Get/Set `sub_slot_index` so official
    `registers.get_by_encoded_id` yields `leaf`. -/
private def emitLeafIndexWire (b : BuilderV1) (leaf : Nat) :
    BuilderV1 × Nat :=
  if leaf == 0 then
    (b, b.zeroTarget)
  else
    let (b1, w) := pushTarget b .constant #[UInt64.ofNat leaf]
    (b1, w.rawIndex)

private def asTargetIndex (w : WireV1) : Except String Nat :=
  match w with
  | .target i => pure i
  | .bool _ => planError "expected target wire, got bool"
  | .u32 _ => planError "expected target wire, got u32 (castFelt first)"

private def asBoolIndex (w : WireV1) : Except String Nat :=
  match w with
  | .bool i => pure i
  | .target _ => planError "expected bool wire, got target"
  | .u32 _ => planError "expected bool wire, got u32"

/-- Cast U32Target → Target (official CastFelt; value-preserving). -/
private def emitCastFelt (b : BuilderV1) (w : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  match w with
  | .target _ => pure (b, w)
  | .u32 _ => pure (pushTarget b .castFelt #[w.operand])
  | .bool _ => planError "castFelt expects target/u32, got bool"

/-- Ensure wire is Target (CastFelt when U32). -/
private def ensureTarget (b : BuilderV1) (w : WireV1) :
    Except String (BuilderV1 × WireV1) :=
  emitCastFelt b w

private def compareOpType : Core.Ops.Cmp → OpTypeV1
  | .eq => .eq | .ne => .eq  -- ne lowered as not(eq)
  | .lt => .lt | .le => .lte | .gt => .gt | .ge => .gte

/-- Emit Get + GetStateCommandResultSingle; returns value wire.
    `sub_slot_index` is a Target wire index whose value is the physical leaf.

    Official `psy_vm` simulate resolution index = **definition step** (not target
    wire index): state cmds with `res == step` run *before* evaluating
    `definitions[step]`. Get must resolve at the GetState def's own step. -/
private def emitStateLoad (b : BuilderV1) (fieldIndex : Nat) :
    BuilderV1 × WireV1 :=
  let leaf := physicalLeafIndex b fieldIndex
  let (b0, slotWireIdx) := emitLeafIndexWire b leaf
  let cmdIdx := b0.cmds.size
  let b1 := {
    b0 with
      cmds := b0.cmds.push
        (.getSelfUserCurrentContractStateSlotSingle (UInt64.ofNat slotWireIdx))
  }
  let (b2, w) := pushTarget b1 .getStateCommandResultSingle #[UInt64.ofNat cmdIdx]
  -- Resolution = definition index of the GetState op (defs.size - 1).
  let getDefStep := b2.defs.size - 1
  let b3 := { b2 with res := b2.res.push getDefStep }
  (b3, w)

/-- Emit Set: `SetContractStateSlotSingle condition leafIdxWire valueWire`.
    The resolution step is the current definition count — all previously
    emitted defs (including the value wire) and before any later def. -/
private def emitStateStore (b : BuilderV1) (fieldIndex : Nat) (cond : WireV1)
    (value : WireV1) : Except String BuilderV1 := do
  let vIdx ← asTargetIndex value
  let cEnc := cond.encoded
  let leaf := physicalLeafIndex b fieldIndex
  let (b0, slotWireIdx) := emitLeafIndexWire b leaf
  let b1 := {
    b0 with
      cmds := b0.cmds.push
        (.setContractStateSlotSingle cEnc (UInt64.ofNat slotWireIdx) (UInt64.ofNat vIdx))
      res := b0.res.push b0.defs.size
  }
  pure b1

/-- Bool AND of two conditions (for nested if guards).
    Official simulate `resolve()`s every op input via encoded id — Bool wires
    must use `(bool<<32)|index`, not bare index (bare would read Target[i]). -/
private def emitBoolAnd (b : BuilderV1) (a c : WireV1) : Except String (BuilderV1 × WireV1) := do
  let _ ← asBoolIndex a
  let _ ← asBoolIndex c
  pure (pushBool b .boolAnd #[a.operand, c.operand])

private def emitBoolOr (b : BuilderV1) (a c : WireV1) : Except String (BuilderV1 × WireV1) := do
  let _ ← asBoolIndex a
  let _ ← asBoolIndex c
  pure (pushBool b .boolOr #[a.operand, c.operand])

private def emitBoolNot (b : BuilderV1) (a : WireV1) : Except String (BuilderV1 × WireV1) := do
  let _ ← asBoolIndex a
  pure (pushBool b .boolNot #[a.operand])

/-- Select mux. Select always yields Target, or Bool for two Bool arms.
    U32 arms pass encoded U32 ids into Target Select. Condition uses the full
    encoded Bool id. -/
private def emitSelect (b : BuilderV1) (cond thenW elseW : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let _ ← asBoolIndex cond
  match thenW, elseW with
  | .bool _, .bool _ =>
      pure (pushBool b .select
        #[cond.operand, thenW.operand, elseW.operand])
  | .bool _, _ | _, .bool _ =>
      planError "Select bool arms must both be bool"
  | _, _ =>
      -- Target/U32/mixed → Target Select with encoded operands
      pure (pushTarget b .select
        #[cond.operand, thenW.operand, elseW.operand])

private def emitConstTarget (b : BuilderV1) (value : UInt64) : BuilderV1 × WireV1 :=
  if value == 0 then (b, zeroWire b)
  else pushTarget b .constant #[value]

private def emitLiteralU64 (b : BuilderV1) (value : UInt64) : BuilderV1 × WireV1 :=
  emitConstTarget b value

/-- Valueless context ops (GetUserId/GetContractId/GetCheckpointId) take the
    canonical `inputs: [0]` Target operand. -/
private def pushValuelessTarget (b : BuilderV1) (op : OpTypeV1) :
    BuilderV1 × WireV1 :=
  pushTarget b op #[0]

/-- Allocate a HashOut valueless context op and return **only** TargetAt limb0.
    Official software eval often stores only the scalar first limb for context
    HashOut ops (no `hash_out_arrays` fill) — TargetAt index≥1 panics. -/
private def emitHashOutLimb0 (b : BuilderV1) (op : OpTypeV1) :
    BuilderV1 × WireV1 :=
  let hashIdx :=
    (b.defs.filter (fun d => d.dataType == .hashOut)).size
  let hashDef : IndexedVarDefV1 := {
    dataType := .hashOut
    index := hashIdx
    opType := op
    inputs := #[0]
  }
  let b1 := { b with defs := b.defs.push hashDef }
  let hashEnc := encodeIndexedId .hashOut hashIdx
  -- limb index 0 = shared zero Target
  pushTarget b1 .targetAt #[hashEnc, UInt64.ofNat b1.zeroTarget]

/-- UInt64 checked add: `sum = l + r`; assert `sum ≥ l` (overflow). -/
private def emitCheckedAdd (b : BuilderV1) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let li ← asTargetIndex l
  let ri ← asTargetIndex r
  let (b1, sum) := pushTarget b .add #[UInt64.ofNat li, UInt64.ofNat ri]
  let (b2, ok) := pushBool b1 .gte #[UInt64.ofNat sum.rawIndex, UInt64.ofNat li]
  let b3 := {
    b2 with
      asserts := b2.asserts.push {
        left := ok.encoded
        right := encodeIndexedId .bool b2.trueBool
        message := "u64 add overflow"
      }
  }
  pure (b3, sum)

private def emitCheckedSub (b : BuilderV1) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let li ← asTargetIndex l
  let ri ← asTargetIndex r
  let (b1, ok) := pushBool b .gte #[UInt64.ofNat li, UInt64.ofNat ri]
  let b2 := {
    b1 with
      asserts := b1.asserts.push {
        left := ok.encoded
        right := encodeIndexedId .bool b1.trueBool
        message := "u64 sub underflow"
      }
  }
  let (b3, diff) := pushTarget b2 .sub #[UInt64.ofNat li, UInt64.ofNat ri]
  pure (b3, diff)

/-- UInt64 checked mul: `prod = l*r`; assert `l==0 || prod/l == r`.
    The safe divisor avoids division by zero when `l==0`. -/
private def emitCheckedMul (b : BuilderV1) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let li ← asTargetIndex l
  let ri ← asTargetIndex r
  let (b1, prod) := pushTarget b .mul #[UInt64.ofNat li, UInt64.ofNat ri]
  let (b2, lIs0) :=
    pushBool b1 .eq #[UInt64.ofNat li, UInt64.ofNat b1.zeroTarget]
  let (b3, oneW) := emitLiteralU64 b2 1
  let oi ← asTargetIndex oneW
  -- safeL = select(l==0, 1, l) so div is never by zero
  let (b4, safeL) ← emitSelect b3 lIs0 (.target oi) l
  let si ← asTargetIndex safeL
  let (b5, quot) :=
    pushTarget b4 .div #[UInt64.ofNat prod.rawIndex, UInt64.ofNat si]
  let (b6, check) :=
    pushBool b5 .eq #[UInt64.ofNat quot.rawIndex, UInt64.ofNat ri]
  let (b7, ok) ← emitBoolOr b6 lIs0 check
  let b8 := {
    b7 with
      asserts := b7.asserts.push {
        left := ok.encoded
        right := encodeIndexedId .bool b7.trueBool
        message := "u64 mul overflow"
      }
  }
  pure (b8, prod)

private def emitCheckedDiv (b : BuilderV1) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let li ← asTargetIndex l
  let ri ← asTargetIndex r
  let (b1, nonzero) :=
    pushBool b .gt #[UInt64.ofNat ri, UInt64.ofNat b.zeroTarget]
  let b2 := {
    b1 with
      asserts := b1.asserts.push {
        left := nonzero.encoded
        right := encodeIndexedId .bool b1.trueBool
        message := "u64 div by zero"
      }
  }
  let (b3, q) := pushTarget b2 .div #[UInt64.ofNat li, UInt64.ofNat ri]
  pure (b3, q)

private def emitCheckedMod (b : BuilderV1) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let li ← asTargetIndex l
  let ri ← asTargetIndex r
  let (b1, nonzero) :=
    pushBool b .gt #[UInt64.ofNat ri, UInt64.ofNat b.zeroTarget]
  let b2 := {
    b1 with
      asserts := b1.asserts.push {
        left := nonzero.encoded
        right := encodeIndexedId .bool b1.trueBool
        message := "u64 mod by zero"
      }
  }
  let (b3, m) := pushTarget b2 .mod_ #[UInt64.ofNat li, UInt64.ofNat ri]
  pure (b3, m)

/-- Target binary op accepting Target/U32 operands (encoded ids). -/
private def emitTargetBin (b : BuilderV1) (op : OpTypeV1) (l r : WireV1) :
    BuilderV1 × WireV1 :=
  pushTarget b op #[l.operand, r.operand]

/-- U32 binary op (U32And/Or/Xor/Shift*). -/
private def emitU32Bin (b : BuilderV1) (op : OpTypeV1) (l r : WireV1) :
    BuilderV1 × WireV1 :=
  pushU32 b op #[l.operand, r.operand]

private def emitCompare (b : BuilderV1) (op : Core.Ops.Cmp) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  -- Comparisons accept Target and encoded U32 operands.
  match op with
  | .ne =>
      let (b1, eqW) := pushBool b .eq #[l.operand, r.operand]
      emitBoolNot b1 eqW
  | other =>
      pure (pushBool b (compareOpType other) #[l.operand, r.operand])

/-- Limb bitwise as Target: U32 op then CastFelt (Plan `.bitAnd`/`.bitOr`/`.bitXor`).
    Faithful only for operands below 2^32, matching the V2 admit contract. -/
private def emitLimbBitwise (b : BuilderV1) (op : OpTypeV1) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let (b1, u) := emitU32Bin b op l r
  emitCastFelt b1 u

/-- Checked UInt64 bitNot: assert `x ≥ 2^32−1` (representable), then Felt
    `(2^32−2) − x` (exact UInt64 bitNot when representable; trap otherwise). -/
private def emitCheckedBitNot (b : BuilderV1) (o : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let oi ← asTargetIndex o
  let (b1, threshold) := emitLiteralU64 b 4294967295  -- 2^32 − 1
  let ti ← asTargetIndex threshold
  let (b2, ok) :=
    pushBool b1 .gte #[UInt64.ofNat oi, UInt64.ofNat ti]
  let b3 := {
    b2 with
      asserts := b2.asserts.push {
        left := ok.encoded
        right := encodeIndexedId .bool b2.trueBool
        message := "u64 bitNot result not representable in Felt"
      }
  }
  let (b4, mask) := emitLiteralU64 b3 4294967294  -- 2^32 − 2 ≡ (2^64−1) (mod p)
  let mi ← asTargetIndex mask
  let (b5, res) :=
    pushTarget b4 .sub #[UInt64.ofNat mi, UInt64.ofNat oi]
  pure (b5, res)

/-- UInt64 shl: assert `count < 64`, then U32ShiftLeft + CastFelt.
    High bits beyond U32 truncate under the frozen DPN operation contract. -/
private def emitUInt64Shl (b : BuilderV1) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let _ ← asTargetIndex l
  let ri ← asTargetIndex r
  let (b1, bound) := emitLiteralU64 b 64
  let bi ← asTargetIndex bound
  let (b2, ok) :=
    pushBool b1 .lt #[UInt64.ofNat ri, UInt64.ofNat bi]
  let b3 := {
    b2 with
      asserts := b2.asserts.push {
        left := ok.encoded
        right := encodeIndexedId .bool b2.trueBool
        message := "invalidShift: count >= 64"
      }
  }
  let (b4, u) := pushU32 b3 .u32ShiftLeft #[l.operand, r.operand]
  emitCastFelt b4 u

/-- UInt64 shr: assert `count < 64`, then U32ShiftRight + CastFelt. -/
private def emitUInt64Shr (b : BuilderV1) (l r : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let _ ← asTargetIndex l
  let ri ← asTargetIndex r
  let (b1, bound) := emitLiteralU64 b 64
  let bi ← asTargetIndex bound
  let (b2, ok) :=
    pushBool b1 .lt #[UInt64.ofNat ri, UInt64.ofNat bi]
  let b3 := {
    b2 with
      asserts := b2.asserts.push {
        left := ok.encoded
        right := encodeIndexedId .bool b2.trueBool
        message := "invalidShift: count >= 64"
      }
  }
  let (b4, u) := pushU32 b3 .u32ShiftRight #[l.operand, r.operand]
  emitCastFelt b4 u

/-- Assert bool wire equals ConstantTrue. -/
private def pushAssertTrue (b : BuilderV1) (cond : WireV1) (msg : String) :
    Except String BuilderV1 := do
  let _ ← asBoolIndex cond
  pure {
    b with
      asserts := b.asserts.push {
        left := cond.encoded
        right := encodeIndexedId .bool b.trueBool
        message := msg
      }
  }

/-- Lower a Plan Expr into a circuit wire under the psy-dpn-v1 admit surface. -/
partial def lowerExprV1 (b : BuilderV1) (params : Array WireV1) :
    Expr → Except String (BuilderV1 × WireV1)
  | .literal v => pure (emitLiteralU64 b v)
  | .boolLiteral true => pure (b, trueWire b)
  | .boolLiteral false => pure (ensureFalse b)
  | .param i =>
      match params[i]? with
      | some w => pure (b, w)
      | none => planError s!"param index {i} out of range"
  | .stateLoad f =>
      pure (emitStateLoad b f)
  | .checkedAdd l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitCheckedAdd b2 lw rw
  | .checkedSub l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitCheckedSub b2 lw rw
  | .checkedMul l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitCheckedMul b2 lw rw
  | .checkedDiv l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitCheckedDiv b2 lw rw
  | .checkedMod l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitCheckedMod b2 lw rw
  | .bitAnd l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitLimbBitwise b2 .u32And lw rw
  | .bitOr l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitLimbBitwise b2 .u32Or lw rw
  | .bitXor l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitLimbBitwise b2 .u32Xor lw rw
  | .compare op l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitCompare b2 op lw rw
  | .select c t e => do
      let (b1, cw) ← lowerExprV1 b params c
      let (b2, tw) ← lowerExprV1 b1 params t
      let (b3, ew) ← lowerExprV1 b2 params e
      emitSelect b3 cw tw ew
  | .boolNot o => do
      let (b1, ow) ← lowerExprV1 b params o
      emitBoolNot b1 ow
  | .shl l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitUInt64Shl b2 lw rw
  | .shr l r => do
      let (b1, lw) ← lowerExprV1 b params l
      let (b2, rw) ← lowerExprV1 b1 params r
      emitUInt64Shr b2 lw rw
  | .checkedBitNot o => do
      let (b1, ow) ← lowerExprV1 b params o
      emitCheckedBitNot b1 ow
  | .ctxUserId =>
      pure (pushValuelessTarget b .getUserId)
  | .ctxContractId =>
      pure (pushValuelessTarget b .getContractId)
  | .ctxCheckpointId =>
      pure (pushValuelessTarget b .getCheckpointId)
  | .ctxNonce =>
      pure (pushValuelessTarget b .getNonce)
  | .ctxCallerContractId =>
      pure (pushValuelessTarget b .getCallerContractId)
  | .ctxUserPublicKeyHash =>
      -- Official executor Target path returns limb0 of user_public_key_hash.
      -- Simulate default injects [0;4] → product 0.
      pure (pushValuelessTarget b .getUserPublicKeyHash)
  | .ctxSessionProofTreeRoot =>
      -- Must be HashOut-typed; Target-only path panics in official software eval.
      pure (emitHashOutLimb0 b .getSessionProofTreeRoot)

/-- Result of lowering a statement sequence: return wires (empty = unit). -/
structure StmtResultV1 where
  builder : BuilderV1
  /-- Return values (Select-merged across branches). Empty = no return. -/
  returnWires : Array WireV1 := #[]
  deriving Inhabited

private def mergeReturns (b : BuilderV1) (cond : WireV1)
    (thenR elseR : Array WireV1) : Except String (BuilderV1 × Array WireV1) := do
  unless thenR.size == elseR.size do
    planError s!"if return arity mismatch then={thenR.size} else={elseR.size}"
  if thenR.isEmpty then
    pure (b, #[])
  else
    let mut bCur := b
    let mut out : Array WireV1 := #[]
    for i in [0:thenR.size] do
      let some t := thenR[i]? | planError "then return missing"
      let some e := elseR[i]? | planError "else return missing"
      let (bSel, w) ← emitSelect bCur cond t e
      bCur := bSel
      out := out.push w
    pure (bCur, out)

/-- Lower statements under an active write condition `writeCond` (bool wire). -/
partial def lowerStmtsV1 (b : BuilderV1) (params : Array WireV1)
    (writeCond : WireV1) :
    List Statement → Except String StmtResultV1
  | [] => pure { builder := b, returnWires := #[] }
  | s :: rest => do
      match s with
      | .store f value => do
          let (b1, vw) ← lowerExprV1 b params value
          let b2 ← emitStateStore b1 f writeCond vw
          lowerStmtsV1 b2 params writeCond rest
      | .returnValue value => do
          let (b1, vw) ← lowerExprV1 b params value
          pure { builder := b1, returnWires := #[vw] }
      | .returnNone =>
          pure { builder := b, returnWires := #[] }
      | .assert cond => do
          let (b1, cw) ← lowerExprV1 b params cond
          -- Under writeCond: assert ( !writeCond \/ cond ) ≡ select(writeCond,cond,true)
          let (b2, gated) ← emitSelect b1 writeCond cw (trueWire b1)
          let b3 ← pushAssertTrue b2 gated "assert"
          lowerStmtsV1 b3 params writeCond rest
      | .assertWithMessage cond msg => do
          let (b1, cw) ← lowerExprV1 b params cond
          let (b2, gated) ← emitSelect b1 writeCond cw (trueWire b1)
          let b3 ← pushAssertTrue b2 gated msg
          lowerStmtsV1 b3 params writeCond rest
      | .ifThenElse cond thenBody elseBody => do
          let (b1, cw) ← lowerExprV1 b params cond
          let (b2, thenCond) ← emitBoolAnd b1 writeCond cw
          let (b3, notC) ← emitBoolNot b2 cw
          let (b4, elseCond) ← emitBoolAnd b3 writeCond notC
          let thenRes ← lowerStmtsV1 b4 params thenCond thenBody.toList
          let elseRes ← lowerStmtsV1 thenRes.builder params elseCond
            elseBody.toList
          let (bFinal, retFinal) ←
            match thenRes.returnWires.isEmpty, elseRes.returnWires.isEmpty with
            | true, true => pure (elseRes.builder, (#[] : Array WireV1))
            | false, false =>
                mergeReturns elseRes.builder cw thenRes.returnWires elseRes.returnWires
            | false, true =>
                planError
                  "if-then returns but else does not (both arms must return or neither)"
            | true, false =>
                planError
                  "if-else returns but then does not (both arms must return or neither)"
          let cont ← lowerStmtsV1 bFinal params writeCond rest
          match retFinal.isEmpty, cont.returnWires.isEmpty with
          | false, true => pure { cont with returnWires := retFinal }
          | true, _ => pure { cont with returnWires := cont.returnWires }
          | false, false =>
              planError "multiple return values in sequence"

/-- Encode return wires as circuit_outputs (target raw index; bool/u32 encoded). -/
private def encodeOutputs (wires : Array WireV1) : Array UInt64 :=
  wires.map fun
    | .target i => UInt64.ofNat i
    | .bool i => encodeIndexedId .bool i
    | .u32 i => encodeIndexedId .u32Target i

/-- General function lower. Multi-leaf state uses physical leaf = fieldIndex
    with Constant leaf-index wires in state commands. -/
def lowerFunctionGeneralV1 (fn : PlanFunction) (multiLeaf : Bool) :
    Except String FunctionCircuitDefV1 := do
  let methodId ← requireMethodIdFromPlanFnV1 fn
  let nParams := fn.params.size
  let (b0, paramWires) := emitParams nParams
  let b0 := { b0 with multiLeaf }
  let b1 := ensurePrelude b0
  let writeCond := trueWire b1
  let res ← lowerStmtsV1 b1 paramWires writeCond fn.body.toList
  let outputs := encodeOutputs res.returnWires
  let mut inputs : Array UInt64 := #[]
  for i in [0:nParams] do
    inputs := inputs.push (UInt64.ofNat i)
  pure {
    name := fn.name
    methodId
    circuitInputs := inputs
    circuitOutputs := outputs
    stateCommands := res.builder.cmds
    stateCommandResolutionIndices := res.builder.res
    assertions := res.builder.asserts
    definitions := res.builder.defs
    events := #[]
  }

/-- Classify a single PlanFunction into a DPN template or general lower. -/
def lowerFunctionV1 (fn : PlanFunction) (multiLeaf : Bool) :
    Except String FunctionCircuitDefV1 := do
  -- Counter templates first (exact target-owned golden) — single-leaf only.
  if !multiLeaf then
    match fn.body.toList with
    | [.returnValue (.stateLoad f)] =>
        return (← lowerViewLoadReturnV1 fn.name f)
    | [.store f (.param 0), .returnNone] =>
        return (← lowerInitializeStoreParamV1 fn.name f)
    | [.store f (.checkedAdd (.stateLoad f2) (.param 0)),
        .returnValue (.stateLoad f3)] => do
        unless f == f2 && f == f3 do
          planError "checkedAdd store/return field mismatch"
        return (← lowerCheckedAddStoreReturnV1 fn.name f)
    | _ => pure ()
  -- General path (if/else, multi-leaf stores, context reads).
  lowerFunctionGeneralV1 fn multiLeaf

/-- Lower an entire Plan to a DPN package. Functions are sorted by name. -/
def lowerPlanToPackageV1 (plan : Plan) : Except String PackageV1 := do
  let nFields := plan.stateFieldNames.size
  unless nFields ≥ 1 do
    planError "expected at least one state field"
  unless nFields ≤ maxStateLeavesV1 do
    planError s!"state leaf count {nFields} exceeds max {maxStateLeavesV1}"
  let multiLeaf := nFields > 1
  let mut out : Array FunctionCircuitDefV1 := #[]
  for fn in plan.functions do
    let d ← lowerFunctionV1 fn multiLeaf
    out := out.push d
  let sorted := out.qsort (fun a b => a.name < b.name)
  pure sorted

/-- Lower a single hand-built PlanFunction (tests / structural probes).
    Pass `multiLeaf := true` for multi-slot shapes. -/
def lowerFunctionForTestV1 (fn : PlanFunction) (multiLeaf : Bool) :
    Except String FunctionCircuitDefV1 :=
  lowerFunctionV1 fn multiLeaf

end ProofForge.Psy.Dpn.Lower
