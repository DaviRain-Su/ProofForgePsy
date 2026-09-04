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
  * Not ported (no Plan constructor produces them): switchOn, narrow/signed
    lanes, pureHelper inlining, storeAggregate/returnAggregate (forLoop/events/
    external calls/IMT/hash gadgets are ported).
  * G5-WIDE: `bindWideUintMul`/`bindWideUintDivMod`/`bindWideUintShift`
    statements and their limb Expr references are ported (schoolbook mul,
    restoring div/mod, fixed bit-width shift), exercised by hand-built Plans.

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

/-- Max guarded static-unroll steps for PSY-LOOP. -/
def maxUnrollBudget : Nat := 64

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

structure HashOutMemoEntry where
  kind : Nat
  argsKey : UInt64
  hashIndex : Nat
  limbs : Array WireV1
  deriving Inhabited

structure ImtMemoEntry where
  kind : Nat
  keyIdx : Nat
  valIdx : Nat
  result : WireV1
  deriving Inhabited
structure WideMulBindV1 where
  operationId : Nat
  limbs : Array WireV1
  deriving Inhabited

structure WideDivBindV1 where
  operationId : Nat
  quotient : Array WireV1
  remainder : Array WireV1
  deriving Inhabited

structure WideShiftBindV1 where
  operationId : Nat
  kind : WideUInt128ShiftKindV1
  limbs : Array WireV1
  deriving Inhabited


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
  /-- Active loop-variable target wires (innermost last). -/
  loopVars : Array WireV1 := #[]
  /-- HashOut CSE table (kind, argsKey) → limbs. -/
  hashOutMemo : Array HashOutMemoEntry := #[]
  /-- IMT CSE table (kind, keyIdx, valIdx) → result wire. -/
  imtMemo : Array ImtMemoEntry := #[]
  /-- G5-WIDE: bindWideUintMul results (Target limbs). -/
  wideMulBinds : Array WideMulBindV1 := #[]
  /-- G5-WIDE: bindWideUintDivMod quotient+remainder limbs. -/
  wideDivBinds : Array WideDivBindV1 := #[]
  /-- G5-WIDE: bindWideUintShift results. -/
  wideShiftBinds : Array WideShiftBindV1 := #[]
  /-- DPN event records emitted by this circuit. -/
  events : Array EventRecordV1 := #[]
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

/-- Fingerprint arg target indices for HashOut CSE (FNV-1a). -/
private def hashOutArgsKey (ins : Array UInt64) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  let prime : UInt64 := 1099511628211
  for x in ins do
    h := (h ^^^ x) * prime
  pure h

/-- Emit one HashOut op (data_type=hashOut) and four TargetAt limbs.
    CSE by (kind, argsKey). -/
private def emitHashOutFull (b : BuilderV1) (kind : Nat) (op : OpTypeV1)
    (inputs : Array UInt64) : BuilderV1 × Array WireV1 := Id.run do
  let key := hashOutArgsKey inputs
  match b.hashOutMemo.find? (fun e => e.kind == kind && e.argsKey == key) with
  | some e => pure (b, e.limbs)
  | none =>
      let hashIdx :=
        (b.defs.filter (fun d => d.dataType == .hashOut)).size
      let hashDef : IndexedVarDefV1 := {
        dataType := .hashOut
        index := hashIdx
        opType := op
        inputs
      }
      let b1 := { b with defs := b.defs.push hashDef }
      let hashEnc := encodeIndexedId .hashOut hashIdx
      let mut bCur := b1
      let mut limbs : Array WireV1 := #[]
      for i in [0:4] do
        -- Constant limb index (cannot call emitLiteralU64 here — defined later).
        let (bL, lit) :=
          if i == 0 then (bCur, zeroWire bCur)
          else pushTarget bCur .constant #[UInt64.ofNat i]
        let (bT, tw) := pushTarget bL .targetAt #[hashEnc, UInt64.ofNat lit.rawIndex]
        bCur := bT
        limbs := limbs.push tw
      let b2 := { bCur with
        hashOutMemo := bCur.hashOutMemo.push
          { kind, argsKey := key, hashIndex := hashIdx, limbs } }
      pure (b2, limbs)

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
/-- Assert `writeCond → cond` (select(writeCond, cond, true)) equals True. -/
private def assertGated (b : BuilderV1) (writeCond cond : WireV1) (msg : String) :
    Except String BuilderV1 := do
  let (b1, gated) ← emitSelect b writeCond cond (trueWire b)
  pushAssertTrue b1 gated msg



/-- Gate a target wire under writeCond: select(writeCond, w, 0). When writeCond
    is the shared ConstantTrue, return `w` unchanged. -/
private def gateTargetUnderCond (b : BuilderV1) (writeCond : WireV1) (w : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  if writeCond == .bool b.trueBool then
    pure (b, w)
  else
    emitSelect b writeCond w (zeroWire b)

/-- Pack UInt64 scalar as 4-limb IMT key/value: [scalar, 0, 0, 0] wire indices. -/
private def emitImtU64As4 (b : BuilderV1) (scalar : WireV1) :
    Except String (BuilderV1 × Array UInt64) := do
  let sIdx ← asTargetIndex scalar
  let z := b.zeroTarget
  pure (b, #[UInt64.ofNat sIdx, UInt64.ofNat z, UInt64.ofNat z, UInt64.ofNat z])

/-- Static base (0) and capacity (2^20) wire indices for IMT commands. -/
private def emitImtBaseCap (b : BuilderV1) : BuilderV1 × Nat × Nat :=
  let baseIdx := b.zeroTarget
  let (b1, capW) := pushTarget b .constant #[UInt64.ofNat 1048576]
  (b1, baseIdx, capW.rawIndex)

/-- Static circuit-side tree height for external/other-user IMT commands.
    Software simulate ignores this field for key-addressed storage. -/
private def imtDefaultTreeHeight : UInt8 := 20

private def lookupImtMemo (b : BuilderV1) (kind keyIdx valIdx : Nat) :
    Option WireV1 :=
  match b.imtMemo.find? (fun e => e.kind == kind && e.keyIdx == keyIdx && e.valIdx == valIdx) with
  | some e => some e.result
  | none => none

private def pushImtMemo (b : BuilderV1) (kind keyIdx valIdx : Nat) (w : WireV1) :
    BuilderV1 :=
  { b with imtMemo := b.imtMemo.push { kind, keyIdx, valIdx, result := w } }

/-- HashOut result limb0 of a state command (GetStateCommandResultHash). -/
private def emitImtHashResultLimb0 (b : BuilderV1) (cmdIdx : Nat) :
    BuilderV1 × WireV1 :=
  let hashIdx :=
    (b.defs.filter (fun d => d.dataType == .hashOut)).size
  let hashDef : IndexedVarDefV1 := {
    dataType := .hashOut
    index := hashIdx
    opType := .getStateCommandResultHash
    inputs := #[UInt64.ofNat cmdIdx]
  }
  let b1 := { b with defs := b.defs.push hashDef }
  let getDefStep := b1.defs.size - 1
  let b2 := { b1 with res := b1.res.push getDefStep }
  let hashEnc := encodeIndexedId .hashOut hashIdx
  pushTarget b2 .targetAt #[hashEnc, UInt64.ofNat b2.zeroTarget]

private def emitImtGet (b : BuilderV1) (keyW : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let kIdx ← asTargetIndex keyW
  if let some w := lookupImtMemo b 0 kIdx 0 then
    pure (b, w)
  else
    let (b0, key4) ← emitImtU64As4 b keyW
    let (b1, baseIdx, capIdx) := emitImtBaseCap b0
    let cmdIdx := b1.cmds.size
    let b2 := {
      b1 with
        cmds := b1.cmds.push
          (.getSelfUserCurrentIMTContractStateValue
            (UInt64.ofNat baseIdx) (UInt64.ofNat capIdx) key4)
    }
    let (b3, w) := emitImtHashResultLimb0 b2 cmdIdx
    pure (pushImtMemo b3 0 kIdx 0 w, w)

/-- IMT set → SetIMTContractStateValue; returns the written value (product ABI).
    Memoized so `let w := set(...); store w; return w` emits one Set. -/
private def emitImtSet (b : BuilderV1) (keyW valueW : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let kIdx ← asTargetIndex keyW
  let vIdx ← asTargetIndex valueW
  if let some w := lookupImtMemo b 2 kIdx vIdx then
    pure (b, w)
  else
    let (b0, key4) ← emitImtU64As4 b keyW
    let (b1, val4) ← emitImtU64As4 b0 valueW
    let (b2, baseIdx, capIdx) := emitImtBaseCap b1
    let cEnc := (trueWire b2).encoded
    let b3 := {
      b2 with
        cmds := b2.cmds.push
          (.setIMTContractStateValue
            cEnc (UInt64.ofNat baseIdx) (UInt64.ofNat capIdx) key4 val4)
        -- Set resolves after current defs (value wires already emitted).
        res := b2.res.push b2.defs.size
    }
    pure (pushImtMemo b3 2 kIdx vIdx valueW, valueW)

/-- IMT contains → ContainsSelfUserCurrentIMT + GetStateCommandResultSingle. -/
private def emitImtContains (b : BuilderV1) (keyW : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let kIdx ← asTargetIndex keyW
  if let some w := lookupImtMemo b 1 kIdx 0 then
    pure (b, w)
  else
    let (b0, key4) ← emitImtU64As4 b keyW
    let (b1, baseIdx, capIdx) := emitImtBaseCap b0
    let cmdIdx := b1.cmds.size
    let b2 := {
      b1 with
        cmds := b1.cmds.push
          (.containsSelfUserCurrentIMTContractStateValue
            (UInt64.ofNat baseIdx) (UInt64.ofNat capIdx) key4)
    }
    let (b3, w) := pushTarget b2 .getStateCommandResultSingle #[UInt64.ofNat cmdIdx]
    let getDefStep := b3.defs.size - 1
    let b4 := { b3 with res := b3.res.push getDefStep }
    pure (pushImtMemo b4 1 kIdx 0 w, w)

/-- IMT getExternal(contractId, key) → GetSelfUserExternalIMT… -/
private def emitImtGetExternal (b : BuilderV1) (cidW keyW : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let cIdx ← asTargetIndex cidW
  let kIdx ← asTargetIndex keyW
  -- kind 3 = external get; memo key = contractIdx in valIdx slot
  if let some w := lookupImtMemo b 3 kIdx cIdx then
    pure (b, w)
  else
    let (b0, key4) ← emitImtU64As4 b keyW
    let (b1, baseIdx, capIdx) := emitImtBaseCap b0
    let cmdIdx := b1.cmds.size
    let b2 := {
      b1 with
        cmds := b1.cmds.push
          (.getSelfUserExternalIMTContractStateValue
            (UInt64.ofNat cIdx) (UInt64.ofNat baseIdx) (UInt64.ofNat capIdx)
            key4 imtDefaultTreeHeight)
    }
    let (b3, w) := emitImtHashResultLimb0 b2 cmdIdx
    pure (pushImtMemo b3 3 kIdx cIdx w, w)

/-- IMT getOther(userId, contractId, key) → GetOtherUserIMT…. -/
private def emitImtGetOther (b : BuilderV1) (uidW cidW keyW : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let uIdx ← asTargetIndex uidW
  let cIdx ← asTargetIndex cidW
  let kIdx ← asTargetIndex keyW
  -- kind 4; fold user+contract into the memo valIdx slot.
  let memoVal := uIdx * 65537 + cIdx
  if let some w := lookupImtMemo b 4 kIdx memoVal then
    pure (b, w)
  else
    let (b0, key4) ← emitImtU64As4 b keyW
    let (b1, baseIdx, capIdx) := emitImtBaseCap b0
    let cmdIdx := b1.cmds.size
    let b2 := {
      b1 with
        cmds := b1.cmds.push
          (.getOtherUserIMTContractStateValue
            (UInt64.ofNat uIdx) (UInt64.ofNat cIdx)
            (UInt64.ofNat baseIdx) (UInt64.ofNat capIdx)
            key4 imtDefaultTreeHeight)
    }
    let (b3, w) := emitImtHashResultLimb0 b2 cmdIdx
    pure (pushImtMemo b3 4 kIdx memoVal w, w)

/-- IMT containsOther(userId, contractId, key). -/
private def emitImtContainsOther (b : BuilderV1) (uidW cidW keyW : WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let uIdx ← asTargetIndex uidW
  let cIdx ← asTargetIndex cidW
  let kIdx ← asTargetIndex keyW
  let memoVal := uIdx * 65537 + cIdx
  if let some w := lookupImtMemo b 5 kIdx memoVal then
    pure (b, w)
  else
    let (b0, key4) ← emitImtU64As4 b keyW
    let (b1, baseIdx, capIdx) := emitImtBaseCap b0
    let cmdIdx := b1.cmds.size
    let b2 := {
      b1 with
        cmds := b1.cmds.push
          (.containsOtherUserIMTContractStateValue
            (UInt64.ofNat uIdx) (UInt64.ofNat cIdx)
            (UInt64.ofNat baseIdx) (UInt64.ofNat capIdx)
            key4 imtDefaultTreeHeight)
    }
    let (b3, w) := pushTarget b2 .getStateCommandResultSingle #[UInt64.ofNat cmdIdx]
    let getDefStep := b3.defs.size - 1
    let b4 := { b3 with res := b3.res.push getDefStep }
    pure (pushImtMemo b4 5 kIdx memoVal w, w)

/-- Deterministic FNV-1a 64-bit hash → Goldilocks Felt, used for the
    external-call qualified-name component hashes. -/
def hashComponentFelt (s : String) : UInt64 := Id.run do
  let prime : UInt64 := 1099511628211
  let mut h : UInt64 := 14695981039346656037
  for c in s.toList do
    h := (h ^^^ c.toNat.toUInt64) * prime
  pure (UInt64.ofNat (h.toNat % 0xFFFFFFFF00000001))

/-- DPN-6 PARTIAL: void externalCall → InvokeExternalContractFunctionSync.
    Hashed static QN components; num_outputs=0 (no response-binding). -/
private def emitVoidExternalCall (b : BuilderV1) (writeCond : WireV1)
    (callee : Array String) (argWires : Array WireV1) :
    Except String BuilderV1 := do
  unless callee.size ≥ 2 do
    planError
      "external callee must have ≥2 qualified-name components (callee.method)"
  let targetHash := hashComponentFelt callee[0]!
  let methodHash := hashComponentFelt callee[1]!
  let (b1, tidW) := emitConstTarget b targetHash
  let (b2, midW) := emitConstTarget b1 methodHash
  let ti ← asTargetIndex tidW
  let mi ← asTargetIndex midW
  let mut args : Array UInt64 := #[]
  for aw in argWires do
    let ai ← asTargetIndex aw
    args := args.push (UInt64.ofNat ai)
  pure {
    b2 with
      cmds := b2.cmds.push
        (.invokeExternalContractFunctionSync
          writeCond.encoded (UInt64.ofNat ti) (UInt64.ofNat mi) args 0)
      -- Official simulate: resolution = definition step, after the hash
      -- Constant defs and arg wires exist.
      res := b2.res.push b2.defs.size
  }

/-- DPN-6: emitEvent → `DPNEventRecord`.
    Event name is source metadata only and is not encoded in the record. -/
private def emitEventRecord (b : BuilderV1) (writeCond : WireV1)
    (argWires : Array WireV1) : Except String BuilderV1 := do
  -- Allocate one set of identity-context operations per emitted event.
  let (b1, cpW) := pushValuelessTarget b .getCheckpointId
  let (b2, userW) := pushValuelessTarget b1 .getUserId
  let (b3, cidW) := pushValuelessTarget b2 .getContractId
  let (b4, cpG) ← gateTargetUnderCond b3 writeCond cpW
  let (b5, userG) ← gateTargetUnderCond b4 writeCond userW
  let (b6, cidG) ← gateTargetUnderCond b5 writeCond cidW
  let mut bCur := b6
  let mut data : Array UInt64 := #[]
  for aw in argWires do
    let (bG, gw) ← gateTargetUnderCond bCur writeCond aw
    bCur := bG
    let ti ← asTargetIndex gw
    data := data.push (UInt64.ofNat ti)
  let cpIdx ← asTargetIndex cpG
  let userIdx ← asTargetIndex userG
  let cidIdx ← asTargetIndex cidG
  let eventRec : EventRecordV1 := {
    condition := writeCond.encoded
    checkpointId := UInt64.ofNat cpIdx
    userId := UInt64.ofNat userIdx
    contractId := UInt64.ofNat cidIdx
    data
  }
  pure { bCur with events := bCur.events.push eventRec }
private def lookupWideMul (b : BuilderV1) (operationId limbIndex : Nat) :
    Except String WireV1 := do
  let some entry := b.wideMulBinds.find? (·.operationId == operationId) |
    planError s!"PSY-DPN-G5: wideUintMulLimb unknown operationId={operationId}"
  match entry.limbs[limbIndex]? with
  | some w => pure w
  | none =>
      planError s!"PSY-DPN-G5: wideUintMulLimb limbIndex={limbIndex} OOR \
(size={entry.limbs.size})"

private def lookupWideDiv (b : BuilderV1)
    (resultKind : WideUInt128DivModResultV1) (operationId limbIndex : Nat) :
    Except String WireV1 := do
  let some entry := b.wideDivBinds.find? (·.operationId == operationId) |
    planError s!"PSY-DPN-G5: wideUintDivModLimb unknown operationId={operationId}"
  let limbs := match resultKind with
    | .quotient => entry.quotient
    | .remainder => entry.remainder
  match limbs[limbIndex]? with
  | some w => pure w
  | none =>
      planError s!"PSY-DPN-G5: wideUintDivModLimb limbIndex={limbIndex} OOR"

private def lookupWideShift (b : BuilderV1)
    (kind : WideUInt128ShiftKindV1) (operationId limbIndex : Nat) :
    Except String WireV1 := do
  let some entry :=
      b.wideShiftBinds.find? (fun e => e.operationId == operationId && e.kind == kind) |
    planError s!"PSY-DPN-G5: wideUintShiftLimb unknown operationId={operationId}"
  match entry.limbs[limbIndex]? with
  | some w => pure w
  | none =>
      planError s!"PSY-DPN-G5: wideUintShiftLimb limbIndex={limbIndex} OOR"


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
  | .hashNoPad args => do
      -- ADR-0039: first HashOut limb (scalar ABI). Full 4-limb uses hashOutLimb.
      unless args.size >= 1 && args.size <= 8 do
        planError s!"hashNoPad arity must be 1..8, got {args.size}"
      let mut bCur := b
      let mut ins : Array UInt64 := #[]
      for a in args do
        let (b1, w) ← lowerExprV1 bCur params a
        let ti ← asTargetIndex w
        bCur := b1
        ins := ins.push (UInt64.ofNat ti)
      let (b2, limbs) := emitHashOutFull bCur 0 .hashNoPad ins
      match limbs[0]? with
      | some w => pure (b2, w)
      | none => planError "hashNoPad limb0 missing"
  | .hashPad args => do
      -- hashPad: Target-typed scalar (official software eval is emit-only no-op).
      unless args.size ≥ 1 && args.size ≤ 8 do
        planError s!"hashPad arity must be 1..8, got {args.size}"
      let mut bCur := b
      let mut ins : Array UInt64 := #[]
      for a in args do
        let (b1, w) ← lowerExprV1 bCur params a
        let ti ← asTargetIndex w
        bCur := b1
        ins := ins.push (UInt64.ofNat ti)
      pure (pushTarget bCur .hashPad ins)
  | .hashTwoToOne args => do
      unless args.size == 8 do
        planError s!"hashTwoToOne requires 8 limbs, got {args.size}"
      let mut bCur := b
      let mut ins : Array UInt64 := #[]
      for a in args do
        let (b1, w) ← lowerExprV1 bCur params a
        let ti ← asTargetIndex w
        bCur := b1
        ins := ins.push (UInt64.ofNat ti)
      let (b2, limbs) := emitHashOutFull bCur 2 .hashTwoToOne ins
      match limbs[0]? with
      | some w => pure (b2, w)
      | none => planError "hashTwoToOne limb0 missing"
  | .hashOutLimb kind limbIndex args => do
      unless kind ≤ 5 do
        planError s!"hashOutLimb kind {kind} out of range"
      unless limbIndex < 4 do
        planError s!"hashOutLimb limbIndex {limbIndex} out of range"
      let mut bCur := b
      let mut ins : Array UInt64 := #[]
      for a in args do
        let (b1, w) ← lowerExprV1 bCur params a
        let ti ← asTargetIndex w
        bCur := b1
        ins := ins.push (UInt64.ofNat ti)
      let op : OpTypeV1 :=
        match kind with
        | 0 => .hashNoPad
        | 1 => .hashPad
        | 2 => .hashTwoToOne
        | 3 => .keccak256
        | 4 => .getUserPublicKeyHash
        | _ => .getSessionProofTreeRoot
      -- Context ops are valueless (inputs [0]); crypto uses lowered args.
      let inputs :=
        if kind ≥ 4 then (#[0] : Array UInt64) else ins
      let (b2, limbs) := emitHashOutFull bCur kind op inputs
      match limbs[limbIndex]? with
      | some w => pure (b2, w)
      | none => planError "hashOutLimb missing"
  | .keccak256 args => do
      -- keccak256: Target-typed first-word ABI (official stores U32TargetArray,
      -- not HashOut arrays — Array4 full ABI is not admitted for keccak).
      unless args.size ≥ 1 && args.size ≤ 16 do
        planError s!"keccak256 arity must be 1..16, got {args.size}"
      let mut bCur := b
      let mut ins : Array UInt64 := #[]
      for a in args do
        let (b1, w) ← lowerExprV1 bCur params a
        let ti ← asTargetIndex w
        bCur := b1
        ins := ins.push (UInt64.ofNat ti)
      pure (pushTarget bCur .keccak256 ins)
  | .imtGet k => do
      let (b1, kw) ← lowerExprV1 b params k
      emitImtGet b1 kw
  | .imtContains k => do
      let (b1, kw) ← lowerExprV1 b params k
      emitImtContains b1 kw
  | .imtSet k v => do
      let (b1, kw) ← lowerExprV1 b params k
      let (b2, vw) ← lowerExprV1 b1 params v
      emitImtSet b2 kw vw
  | .imtGetExternal c k => do
      let (b1, cw) ← lowerExprV1 b params c
      let (b2, kw) ← lowerExprV1 b1 params k
      emitImtGetExternal b2 cw kw
  | .imtGetOther u c k => do
      let (b1, uw) ← lowerExprV1 b params u
      let (b2, cw) ← lowerExprV1 b1 params c
      let (b3, kw) ← lowerExprV1 b2 params k
      emitImtGetOther b3 uw cw kw
  | .imtContainsOther u c k => do
      let (b1, uw) ← lowerExprV1 b params u
      let (b2, cw) ← lowerExprV1 b1 params c
      let (b3, kw) ← lowerExprV1 b2 params k
      emitImtContainsOther b3 uw cw kw
  | .wideUintMulLimb _bitWidth operationId limbIndex => do
      let w ← lookupWideMul b operationId limbIndex
      pure (b, w)
  | .wideUintDivModLimb resultKind _bitWidth operationId limbIndex => do
      let w ← lookupWideDiv b resultKind operationId limbIndex
      pure (b, w)
  | .wideUintShiftLimb kind _bitWidth operationId limbIndex => do
      let w ← lookupWideShift b kind operationId limbIndex
      pure (b, w)
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

/-- Snapshot operands + optional UInt32 range assert (`limb < 2^32`). -/
private def lowerWideOperandLimbs (b : BuilderV1) (params : Array WireV1)
    (writeCond : WireV1) (limbs : Array Expr)
    (rangeMsg : String) (checkRange : Bool) :
    Except String (BuilderV1 × Array WireV1) := do
  let mut bCur := b
  let mut out : Array WireV1 := #[]
  let (bLim, limW) := emitLiteralU64 bCur 4294967296
  bCur := bLim
  for e in limbs do
    let (b1, w0) ← lowerExprV1 bCur params e
    bCur := b1
    if checkRange then
      let (b2, ok) ← emitCompare bCur .lt w0 limW
      bCur ← assertGated b2 writeCond ok rangeMsg
      let (b3, safe) ← emitSelect bCur ok w0 (zeroWire bCur)
      bCur := b3
      out := out.push safe
    else
      out := out.push w0
  pure (bCur, out)

/-- Schoolbook wide mul: UInt{N} limbs → 2N UInt16 digits → double-width product
    with per-product U32 normalization; high half must be zero (checked
    overflow). Result limbs are bound under operationId. -/
private def emitBindWideUintMulV1 (b : BuilderV1) (params : Array WireV1)
    (writeCond : WireV1)
    (bitWidth operationId : Nat) (lhs rhs : Array Expr) :
    Except String BuilderV1 := do
  unless bitWidth == 128 || bitWidth == 256 do
    planError "PSY-DPN-G5: bindWideUintMul bitWidth must be 128 or 256"
  let limbCount := bitWidth / 32
  let digitCount := limbCount * 2
  let productDigits := digitCount * 2
  unless lhs.size == limbCount && rhs.size == limbCount do
    planError s!"PSY-DPN-G5: bindWideUintMul requires two {limbCount}-limb operands"
  let (b0, left) ← lowerWideOperandLimbs b params writeCond lhs
    "u32 limb out of range" true
  let (b1, right) ← lowerWideOperandLimbs b0 params writeCond rhs
    "u32 limb out of range" true
  let (b2, mask) := emitLiteralU64 b1 65535
  let (b3, shift) := emitLiteralU64 b2 16
  let (b4, base) := emitLiteralU64 b3 65536
  let mut bCur := b4
  -- UInt32 limbs -> LE UInt16 digits (U32And / U32ShiftRight), kept as U32 wires.
  let mut lhsDigits : Array WireV1 := #[]
  let mut rhsDigits : Array WireV1 := #[]
  for limb in left do
    let (bLo, lo) := emitU32Bin bCur .u32And limb mask
    let (bSh, shifted) := emitU32Bin bLo .u32ShiftRight limb shift
    let (bHi, hi) := emitU32Bin bSh .u32And shifted mask
    bCur := bHi
    lhsDigits := lhsDigits.push lo
    lhsDigits := lhsDigits.push hi
  for limb in right do
    let (bLo, lo) := emitU32Bin bCur .u32And limb mask
    let (bSh, shifted) := emitU32Bin bLo .u32ShiftRight limb shift
    let (bHi, hi) := emitU32Bin bSh .u32And shifted mask
    bCur := bHi
    rhsDigits := rhsDigits.push lo
    rhsDigits := rhsDigits.push hi
  -- digits[i] = sum over j of lhsDigits[j]*rhsDigits[i-j] (U32).
  let mut digits : Array WireV1 := #[]
  for i in [0:productDigits] do
    let mut acc : WireV1 := zeroWire bCur
    for j in [0:digitCount] do
      if j ≤ i && i - j < digitCount then
        let some lj := lhsDigits[j]? | planError "PSY-DPN-G5: mul digit lhs"
        let some rk := rhsDigits[i - j]? | planError "PSY-DPN-G5: mul digit rhs"
        let (bP, p) := emitU32Bin bCur .u32Mul lj rk
        let (bA, s) := emitU32Bin bP .u32Add acc p
        bCur := bA
        acc := s
    digits := digits.push acc
  -- Normalize per digit: carry = (digit + carry) >> 16, digit &= 0xFFFF.
  let mut carry : WireV1 := zeroWire bCur
  for i in [0:productDigits] do
    let some d := digits[i]? | planError "PSY-DPN-G5: mul digit norm"
    let (bS, sum) := emitU32Bin bCur .u32Add d carry
    let (bC, c) := emitU32Bin bS .u32ShiftRight sum shift
    let (bM, m) := emitU32Bin bC .u32And sum mask
    bCur := bM
    digits := digits.set! i m
    carry := c
  -- Overflow: high half (digitCount..productDigits) must be zero.
  let overflowMsg := if bitWidth == 256 then "u256 mul overflow" else "u128 mul overflow"
  let (bZ, zEq) ← emitCompare bCur .eq carry (zeroWire bCur)
  bCur := bZ
  let mut noOverflow : WireV1 := zEq
  for i in [digitCount:productDigits] do
    let some digit := digits[i]? | planError "PSY-DPN-G5: wide product digit missing"
    let (bE, dEq) ← emitCompare bCur .eq digit (zeroWire bCur)
    let (bA, andW) ← emitBoolAnd bE noOverflow dEq
    bCur := bA
    noOverflow := andW
  bCur ← assertGated bCur writeCond noOverflow "u64 mul overflow"
  -- Repack low UInt16 digits into UInt32 Target limbs.
  let mut resultLimbs : Array WireV1 := #[]
  for limbIndex in [0:limbCount] do
    let loIndex := limbIndex * 2
    let hiIndex := loIndex + 1
    let some lo := digits[loIndex]? | planError "PSY-DPN-G5: wide mul low result digit missing"
    let some hi := digits[hiIndex]? | planError "PSY-DPN-G5: wide mul high result digit missing"
    let (bSc, scaledHigh) := emitTargetBin bCur .mul hi base
    let (bSm, limb) := emitTargetBin bSc .add lo scaledHigh
    bCur := bSm
    resultLimbs := resultLimbs.push limb
  pure {
    bCur with
      wideMulBinds := bCur.wideMulBinds.push {
        operationId, limbs := resultLimbs
      }
  }

/-- Lexicographic remainder ≥ divisor (remainder is one limb wider). -/
private def emitWideDivLexGe (b : BuilderV1)
    (remainder divisor : Array WireV1) :
    Except String (BuilderV1 × WireV1) := do
  let limbCount := divisor.size
  unless remainder.size == limbCount + 1 do
    planError "PSY-DPN-G5: wide div lexGe remainder width mismatch"
  let mut bCur := b
  let some r0 := remainder[0]? | planError "PSY-DPN-G5: rem0"
  let some d0 := divisor[0]? | planError "PSY-DPN-G5: div0"
  let (b0, acc0) ← emitCompare bCur .ge r0 d0
  bCur := b0
  let mut acc := acc0
  for i in [1:limbCount] do
    let some ri := remainder[i]? | planError "PSY-DPN-G5: rem i"
    let some di := divisor[i]? | planError "PSY-DPN-G5: div i"
    let (bGt, limbGt) ← emitCompare bCur .gt ri di
    let (bEq, limbEq) ← emitCompare bGt .eq ri di
    let (bAnd, eqAnd) ← emitBoolAnd bEq limbEq acc
    let (bOr, next) ← emitBoolOr bAnd limbGt eqAnd
    bCur := bOr
    acc := next
  let some rHi := remainder[limbCount]? | planError "PSY-DPN-G5: rem hi"
  let (bNe, hiNe) ← emitCompare bCur .ne rHi (zeroWire bCur)
  let (bOr2, final) ← emitBoolOr bNe hiNe acc
  pure (bOr2, final)

/-- One restoring step (single bit) of the wide divider (SSA form). -/
private def emitWideDivOneStep (b : BuilderV1)
    (limbCount : Nat) (sourceBit : WireV1)
    (remainder quotient divisor : Array WireV1)
    (divisorZero : WireV1) (writeCond : WireV1) :
    Except String (BuilderV1 × Array WireV1 × Array WireV1) := do
  unless remainder.size == limbCount + 1 && quotient.size == limbCount
      && divisor.size == limbCount do
    planError "PSY-DPN-G5: wide div step shape mismatch"
  let (bS1, shiftTop) := emitLiteralU64 b 31
  let (bS2, shiftOne) := emitLiteralU64 bS1 1
  let (bS3, base) := emitLiteralU64 bS2 4294967296
  let (bS4, one) := emitLiteralU64 bS3 1
  let mut bCur := bS4
  -- Shift remainder left by 1, inject source bit into limb 0.
  let mut carries : Array WireV1 := #[]
  for i in [0:limbCount] do
    let some ri := remainder[i]? | planError "PSY-DPN-G5: rem carry"
    let (bC, c) := emitU32Bin bCur .u32ShiftRight ri shiftTop
    bCur := bC
    carries := carries.push c
  let some r0 := remainder[0]? | planError "PSY-DPN-G5: r0"
  let (bL0, r0s) := emitU32Bin bCur .u32ShiftLeft r0 shiftOne
  let (bR0, r0n) := emitU32Bin bL0 .u32Or r0s sourceBit
  bCur := bR0
  let mut newRem : Array WireV1 := #[r0n]
  for i in [1:limbCount] do
    let some ri := remainder[i]? | planError "PSY-DPN-G5: rem shift"
    let some cPrev := carries[i - 1]? | planError "PSY-DPN-G5: carry prev"
    let (bLs, ris) := emitU32Bin bCur .u32ShiftLeft ri shiftOne
    let (bOr, rin) := emitU32Bin bLs .u32Or ris cPrev
    bCur := bOr
    newRem := newRem.push rin
  let some cLast := carries[limbCount - 1]? | planError "PSY-DPN-G5: carry last"
  newRem := newRem.push cLast
  -- take := rem >= divisor
  let (bTk, take) ← emitWideDivLexGe bCur newRem divisor
  bCur := bTk
  -- subtract with borrow when take
  let mut borrow : WireV1 := zeroWire bCur
  let mut diffs : Array WireV1 := #[]
  for i in [0:limbCount] do
    let some ri := newRem[i]? | planError "PSY-DPN-G5: sub rem"
    let some di := divisor[i]? | planError "PSY-DPN-G5: sub div"
    let (bSub, sub) := emitTargetBin bCur .add di borrow
    let (bUn, under) ← emitCompare bSub .lt ri sub
    let (bDir, direct) := emitTargetBin bUn .sub ri sub
    let (bW0, wrapped0) := emitTargetBin bDir .add ri base
    let (bW1, wrapped) := emitTargetBin bW0 .sub wrapped0 sub
    let (bDf, diff) ← emitSelect bW1 under wrapped direct
    let (bBr, br) ← emitSelect bDf under one (zeroWire bDf)
    bCur := bBr
    diffs := diffs.push diff
    borrow := br
  let some rHi := newRem[limbCount]? | planError "PSY-DPN-G5: rHi"
  -- high_ok := !take \/ rHi == borrow
  let (bNt, notTake) ← emitBoolNot bCur take
  let (bEq, hiEq) ← emitCompare bNt .eq rHi borrow
  let (bOk, highOk) ← emitBoolOr bEq notTake hiEq
  let (bDz, skipOrOk) ← emitBoolOr bOk divisorZero highOk
  bCur ← assertGated bDz writeCond skipOrOk "u128 div internal high borrow"
  let (bHd, highDiff) := emitTargetBin bCur .sub rHi borrow
  bCur := bHd
  let mut remOut : Array WireV1 := #[]
  for i in [0:limbCount] do
    let some ri := newRem[i]? | planError "PSY-DPN-G5: rem out"
    let some di := diffs[i]? | planError "PSY-DPN-G5: diff out"
    let (bSel, r) ← emitSelect bCur take di ri
    bCur := bSel
    remOut := remOut.push r
  let (bRh, rH) ← emitSelect bCur take highDiff rHi
  bCur := bRh
  remOut := remOut.push rH
  let (bRz, remHiOk) ← emitCompare bCur .eq rH (zeroWire bCur)
  let (bRz2, remHiGate) ← emitBoolOr bRz divisorZero remHiOk
  bCur ← assertGated bRz2 writeCond remHiGate "u128 div internal remainder high"
  -- quotient <<= 1 | take
  let (bQb, qbit) ← emitSelect bCur take one (zeroWire bCur)
  bCur := bQb
  let mut qCarries : Array WireV1 := #[]
  for i in [0:limbCount] do
    let some qi := quotient[i]? | planError "PSY-DPN-G5: q carry"
    let (bC, c) := emitU32Bin bCur .u32ShiftRight qi shiftTop
    bCur := bC
    qCarries := qCarries.push c
  let some q0 := quotient[0]? | planError "PSY-DPN-G5: q0"
  let (bQl, q0s) := emitU32Bin bCur .u32ShiftLeft q0 shiftOne
  let (bQo, q0n) := emitU32Bin bQl .u32Or q0s qbit
  bCur := bQo
  let mut quotOut : Array WireV1 := #[q0n]
  for i in [1:limbCount] do
    let some qi := quotient[i]? | planError "PSY-DPN-G5: q shift"
    let some cPrev := qCarries[i - 1]? | planError "PSY-DPN-G5: qc"
    let (bLs, qis) := emitU32Bin bCur .u32ShiftLeft qi shiftOne
    let (bOr, qin) := emitU32Bin bLs .u32Or qis cPrev
    bCur := bOr
    quotOut := quotOut.push qin
  let some qcLast := qCarries[limbCount - 1]? | planError "PSY-DPN-G5: qc last"
  let (bQe, qov) ← emitCompare bCur .eq qcLast (zeroWire bCur)
  let (bQe2, qovGate) ← emitBoolOr bQe divisorZero qov
  bCur ← assertGated bQe2 writeCond qovGate "u128 div internal quotient overflow"
  pure (bCur, remOut, quotOut)

/-- Extract bit `31 - step` of a limb as U32 0/1 (MSB-first within limb). -/
private def emitLimbBitMSB (b : BuilderV1) (limb : WireV1) (stepInLimb : Nat) :
    Except String (BuilderV1 × WireV1) := do
  unless stepInLimb < 32 do
    planError "PSY-DPN-G5: limb bit step must be < 32"
  let dist := 31 - stepInLimb
  let (b1, distW) := emitLiteralU64 b (UInt64.ofNat dist)
  let (b2, shifted) := emitU32Bin b1 .u32ShiftRight limb distW
  let (b3, one) := emitLiteralU64 b2 1
  pure (emitU32Bin b3 .u32And shifted one)

/-- Restoring wide div/mod binding, fully unrolled. -/
private def emitBindWideUintDivModV1 (b : BuilderV1) (params : Array WireV1)
    (writeCond : WireV1)
    (resultKind : WideUInt128DivModResultV1)
    (bitWidth operationId : Nat) (lhs rhs : Array Expr) :
    Except String BuilderV1 := do
  unless bitWidth == 128 || bitWidth == 256 do
    planError "PSY-DPN-G5: bindWideUintDivMod bitWidth must be 128 or 256"
  let limbCount := bitWidth / 32
  unless lhs.size == limbCount && rhs.size == limbCount do
    planError s!"PSY-DPN-G5: bindWideUintDivMod requires two {limbCount}-limb operands"
  let rangeMsg := if bitWidth == 256 then "u256 div operand limb out of range"
    else "u128 div operand limb out of range"
  let zeroMessage := match resultKind, bitWidth with
    | .quotient, 256 => "u256 div by zero"
    | .remainder, 256 => "u256 mod by zero"
    | .quotient, _ => "u128 div by zero"
    | .remainder, _ => "u128 mod by zero"
  let (b0, left) ← lowerWideOperandLimbs b params writeCond lhs rangeMsg true
  let (b1, right) ← lowerWideOperandLimbs b0 params writeCond rhs rangeMsg true
  let mut bCur := b1
  -- divisorZero := all limbs == 0
  let some r0 := right[0]? | planError "PSY-DPN-G5: rhs0"
  let (bZ0, dz0) ← emitCompare bCur .eq r0 (zeroWire bCur)
  bCur := bZ0
  let mut divisorZero := dz0
  for i in [1:limbCount] do
    let some ri := right[i]? | planError "PSY-DPN-G5: rhs i"
    let (bE, eqW) ← emitCompare bCur .eq ri (zeroWire bCur)
    let (bA, andW) ← emitBoolAnd bE divisorZero eqW
    bCur := bA
    divisorZero := andW
  let (bNz, notZero) ← emitBoolNot bCur divisorZero
  bCur ← assertGated bNz writeCond notZero zeroMessage
  let mut rem : Array WireV1 := #[]
  for _ in [0:limbCount + 1] do
    rem := rem.push (zeroWire bCur)
  let mut quot : Array WireV1 := #[]
  for _ in [0:limbCount] do
    quot := quot.push (zeroWire bCur)
  for sourceIndex in List.range limbCount |>.reverse do
    let some source := left[sourceIndex]? |
      planError "PSY-DPN-G5: dividend limb missing"
    for step in [0:32] do
      let (bBit, bit) ← emitLimbBitMSB bCur source step
      let (bSt, rem', quot') ←
        emitWideDivOneStep bBit limbCount bit rem quot right divisorZero writeCond
      bCur := bSt
      rem := rem'
      quot := quot'
  let mut qOut : Array WireV1 := #[]
  for w in quot do
    let (bT, t) ← ensureTarget bCur w
    bCur := bT
    qOut := qOut.push t
  let mut rOut : Array WireV1 := #[]
  for i in [0:limbCount] do
    let some w := rem[i]? | planError "PSY-DPN-G5: rem bind"
    let (bT, t) ← ensureTarget bCur w
    bCur := bT
    rOut := rOut.push t
  pure {
    bCur with
      wideDivBinds := bCur.wideDivBinds.push {
        operationId, quotient := qOut, remainder := rOut
      }
  }

/-- Exact wide logical shift: fixed bitWidth one-bit walk. -/
private def emitBindWideUintShiftV1 (b : BuilderV1) (params : Array WireV1)
    (writeCond : WireV1)
    (kind : WideUInt128ShiftKindV1) (bitWidth operationId : Nat)
    (value : Array Expr) (count : Expr) :
    Except String BuilderV1 := do
  unless bitWidth == 128 || bitWidth == 256 do
    planError "PSY-DPN-G5: bindWideUintShift bitWidth must be 128 or 256"
  let limbCount := bitWidth / 32
  unless value.size == limbCount do
    planError s!"PSY-DPN-G5: bindWideUintShift requires {limbCount} value limbs"
  let rangeMsg := if bitWidth == 256 then "u256 shift operand limb out of range"
    else "u128 shift operand limb out of range"
  let overflowMsg := if bitWidth == 256 then "u256 shl overflow" else "u128 shl overflow"
  let (b0, limbs0) ← lowerWideOperandLimbs b params writeCond value rangeMsg true
  let (b1, countW) ← lowerExprV1 b0 params count
  let (b2, bwLit) := emitLiteralU64 b1 (UInt64.ofNat bitWidth)
  let (b3, countOk) ← emitCompare b2 .lt countW bwLit
  let mut bCur ← assertGated b3 writeCond countOk
    s!"invalidShift: count >= {bitWidth}"
  let (bOne, one) := emitLiteralU64 bCur 1
  let (bTop, shiftTop) := emitLiteralU64 bOne 31
  let (bSo, shiftOne) := emitLiteralU64 bTop 1
  bCur := bSo
  let mut limbs := limbs0
  for step in [0:bitWidth] do
    let (bSt, stepLit) := emitLiteralU64 bCur (UInt64.ofNat step)
    let (bTk, take) ← emitCompare bSt .lt stepLit countW
    bCur := bTk
    match kind with
    | .shl => do
        let mut carries : Array WireV1 := #[]
        for i in [0:limbCount] do
          let some li := limbs[i]? | planError "PSY-DPN-G5: shl carry"
          let (bC, c) := emitU32Bin bCur .u32ShiftRight li shiftTop
          bCur := bC
          carries := carries.push c
        let some cLast := carries[limbCount - 1]? | planError "PSY-DPN-G5: shl ov"
        let (bNt, notTake) ← emitBoolNot bCur take
        let (bEq, cZero) ← emitCompare bNt .eq cLast (zeroWire bNt)
        let (bOk, ok) ← emitBoolOr bEq notTake cZero
        bCur ← assertGated bOk writeCond ok overflowMsg
        let some l0 := limbs[0]? | planError "PSY-DPN-G5: shl l0"
        let (bL, l0s) := emitU32Bin bCur .u32ShiftLeft l0 shiftOne
        let (bS0, l0n) ← emitSelect bL take l0s l0
        bCur := bS0
        let mut next : Array WireV1 := #[l0n]
        for i in [1:limbCount] do
          let some li := limbs[i]? | planError "PSY-DPN-G5: shl li"
          let some cPrev := carries[i - 1]? | planError "PSY-DPN-G5: shl cp"
          let (bLs, lis) := emitU32Bin bCur .u32ShiftLeft li shiftOne
          let (bOr, lior) := emitU32Bin bLs .u32Or lis cPrev
          let (bSel, lin) ← emitSelect bOr take lior li
          bCur := bSel
          next := next.push lin
        limbs := next
    | .shr => do
        let mut lowBits : Array WireV1 := #[]
        for i in [0:limbCount] do
          let some li := limbs[i]? | planError "PSY-DPN-G5: shr low"
          let (bL, lb) := emitU32Bin bCur .u32And li one
          bCur := bL
          lowBits := lowBits.push lb
        let mut next : Array WireV1 := #[]
        for idx in [0:limbCount - 1] do
          let some li := limbs[idx]? | planError "PSY-DPN-G5: shr idx"
          let some lbNext := lowBits[idx + 1]? | planError "PSY-DPN-G5: shr lb"
          let (bRs2, lis) := emitU32Bin bCur .u32ShiftRight li shiftOne
          let (bSh, moved) := emitU32Bin bRs2 .u32ShiftLeft lbNext shiftTop
          let (bOr, lior) := emitU32Bin bSh .u32Or lis moved
          let (bSel, lin) ← emitSelect bOr take lior li
          bCur := bSel
          next := next.push lin
        let some lLast := limbs[limbCount - 1]? | planError "PSY-DPN-G5: shr last"
        let (bRs, lastS) := emitU32Bin bCur .u32ShiftRight lLast shiftOne
        let (bSl, lastN) ← emitSelect bRs take lastS lLast
        bCur := bSl
        next := next.push lastN
        limbs := next
  let mut outLimbs : Array WireV1 := #[]
  for w in limbs do
    let (bT, t) ← ensureTarget bCur w
    bCur := bT
    outLimbs := outLimbs.push t
  pure {
    bCur with
      wideShiftBinds := bCur.wideShiftBinds.push {
        operationId, kind, limbs := outLimbs
      }
  }

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
      | .returnAggregate values => do
          unless values.size ≥ 1 && values.size ≤ 8 do
            planError s!"aggregate return arity must be 1..8, got {values.size}"
          let mut bCur := b
          let mut wires : Array WireV1 := #[]
          for v in values do
            let (b1, w) ← lowerExprV1 bCur params v
            bCur := b1
            wires := wires.push w
          pure { builder := bCur, returnWires := wires }
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

      | .forLoop start endExclusive maxIter body => do
          unless maxIter ≤ maxUnrollBudget do
            planError s!"bounded for maxIterations={maxIter} exceeds unroll \
budget {maxUnrollBudget} (no while/unbounded; PSY-LOOP)"
          let (b1, startW) ← lowerExprV1 b params start
          let (b2, endW) ← lowerExprV1 b1 params endExclusive
          let si ← asTargetIndex startW
          let ei ← asTargetIndex endW
          -- if start < end { assert end - start <= maxIter }
          let (b3, rangeNonempty) :=
            pushBool b2 .lt #[UInt64.ofNat si, UInt64.ofNat ei]
          let (b4, span) :=
            pushTarget b3 .sub #[UInt64.ofNat ei, UInt64.ofNat si]
          let (b5, maxLit) := emitLiteralU64 b4 (UInt64.ofNat maxIter)
          let mi ← asTargetIndex maxLit
          let (b6, fits) :=
            pushBool b5 .lte #[UInt64.ofNat span.rawIndex, UInt64.ofNat mi]
          let (b7, gatedFits) ← emitSelect b6 rangeNonempty fits (trueWire b6)
          let b8 := {
            b7 with
              asserts := b7.asserts.push {
                left := gatedFits.encoded
                right := encodeIndexedId .bool b7.trueBool
                message := "boundExceeded"
              }
          }
          -- Unroll: for k in 0..maxIter-1:
          --   i = start + k; if i < end { body with loopVar = i }
          let mut bCur := b8
          for k in [0:maxIter] do
            let (bK, kLit) := emitLiteralU64 bCur (UInt64.ofNat k)
            let ki ← asTargetIndex kLit
            let (bI, iW) :=
              pushTarget bK .add #[UInt64.ofNat si, UInt64.ofNat ki]
            let ii ← asTargetIndex iW
            let (bG, stepGuard) :=
              pushBool bI .lt #[UInt64.ofNat ii, UInt64.ofNat ei]
            let (bC, stepCond) ← emitBoolAnd bG writeCond stepGuard
            let bLoop := { bC with loopVars := bC.loopVars.push iW }
            let bodyRes ← lowerStmtsV1 bLoop params stepCond body.toList
            unless bodyRes.returnWires.isEmpty do
              planError "return inside bounded for is not admitted in this slice"
            -- Pop loop var
            bCur := { bodyRes.builder with loopVars := bC.loopVars }
          let cont ← lowerStmtsV1 bCur params writeCond rest
          pure cont
      | .emitEvent _name args => do
          let mut bCur := b
          let mut argWires : Array WireV1 := #[]
          for a in args do
            let (b1, w) ← lowerExprV1 bCur params a
            bCur := b1
            argWires := argWires.push w
          let b2 ← emitEventRecord bCur writeCond argWires
          lowerStmtsV1 b2 params writeCond rest
      | .externalCall callee args => do
          -- DPN-6 PARTIAL: void sync call only (result-bearing FC at Plan).
          let mut bCur := b
          let mut argWires : Array WireV1 := #[]
          for a in args do
            let (b1, w) ← lowerExprV1 bCur params a
            bCur := b1
            argWires := argWires.push w
          let b2 ← emitVoidExternalCall bCur writeCond callee argWires
          lowerStmtsV1 b2 params writeCond rest
      | .bindWideUintMul bitWidth operationId lhs rhs => do
          let b1 ← emitBindWideUintMulV1 b params writeCond
            bitWidth operationId lhs rhs
          lowerStmtsV1 b1 params writeCond rest
      | .bindWideUintDivMod resultKind bitWidth operationId lhs rhs => do
          let b1 ← emitBindWideUintDivModV1 b params writeCond
            resultKind bitWidth operationId lhs rhs
          lowerStmtsV1 b1 params writeCond rest
      | .bindWideUintShift kind bitWidth operationId value count => do
          let b1 ← emitBindWideUintShiftV1 b params writeCond
            kind bitWidth operationId value count
          lowerStmtsV1 b1 params writeCond rest

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
    events := res.builder.events
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
