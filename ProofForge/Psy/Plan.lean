import ProofForge.Core.Ops

namespace ProofForge.Psy.Plan

/-!
# Psy Plan — target-owned IR between extracted Core ops and the DPN package

This is the psy-dpn-v1 slice of the ProofForgeV2 Psy `Plan` surface
(`proof_forge` `Targets/Psy/LowerSemanticV1.lean`), specialized to what the
Lean extractor in this repository can produce:

* Felt-carried `UInt64`/`Bool` scalars only — no narrow/signed/wide lanes.
* No `pureHelper` (the extractor erases `@[pf_inline]` helpers before Core ops).
* No events, external calls, schedules, IMT, or hashing (no `OpExt`).
* No `forLoop`/`switchOn` (extracted loops fail closed in v1; `match` reaches
  us as nested `ite`).
* No aggregate returns (single Felt result or unit).

Expressions are Goldilocks-Felt circuits; every `UInt64` arithmetic node is
checked (overflow traps as an unsatisfiable assertion at proof time). Plain
Lean wrapping `+`/`-`/`*`/`/`/`%` on `UInt64` lower to the checked variants:
on Psy there is no faithful wrapping interpretation, so we trap instead.
-/

/-- Which exact UInt128 div/mod result a target-owned restoring binding exposes. -/
inductive WideUInt128DivModResultV1 where
  | quotient
  | remainder
  deriving BEq, Inhabited, Repr

/-- Direction of an exact UInt128 shift binding (count is UInt32 Felt). -/
inductive WideUInt128ShiftKindV1 where
  | shl
  | shr
  deriving BEq, Inhabited, Repr

/-- Plan expression over Felt-carried UInt64/Bool scalars. -/
inductive Expr where
  | literal (value : UInt64)
  | boolLiteral (value : Bool)
  | param (inputIndex : Nat)
  | stateLoad (fieldIndex : Nat)
  | checkedAdd (lhs rhs : Expr)
  | checkedSub (lhs rhs : Expr)
  | checkedMul (lhs rhs : Expr)
  | checkedDiv (lhs rhs : Expr)
  | checkedMod (lhs rhs : Expr)
  | compare (op : Core.Ops.Cmp) (lhs rhs : Expr)
  | bitAnd (lhs rhs : Expr)
  | bitOr (lhs rhs : Expr)
  | bitXor (lhs rhs : Expr)
  | boolNot (operand : Expr)
  | shl (lhs rhs : Expr)
  | shr (lhs rhs : Expr)
  /-- Checked UInt64 bitwise-not: exact only when the operand is ≥ 2^32−1
      (result representable below Goldilocks); the emitter asserts the
      threshold, mirroring the V2 `checkedBitNot` contract. -/
  | checkedBitNot (operand : Expr)
  | ctxUserId
  | ctxContractId
  | ctxCheckpointId
  | ctxNonce
  | ctxCallerContractId
  | ctxUserPublicKeyHash
  | ctxSessionProofTreeRoot
  /-- ADR-0039 Poseidon gadgets, scalar product ABI (first HashOut limb).
      Arity 1..8 (hashNoPad/hashPad), exactly 8 (hashTwoToOne), 1..16
      (keccak256). -/
  | hashNoPad (args : Array Expr)
  | hashPad (args : Array Expr)
  | hashTwoToOne (args : Array Expr)
  | keccak256 (args : Array Expr)
  /-- Full HashOut multi-limb product ABI: one limb (0..3) of a HashOut op.
      `kind`: 0=hashNoPad, 1=hashPad, 2=hashTwoToOne, 3=keccak256,
      4=userPublicKeyHash, 5=sessionProofTreeRoot. Full Array4 ABI is
      admitted only for hashNoPad/hashTwoToOne (official simulate fills
      hash_out_arrays); keccak/context stay limb0. -/
  | hashOutLimb (kind limbIndex : Nat) (args : Array Expr)
  /-- IMT self-current pilot: UInt64 key/value packed as [scalar, 0, 0, 0]
      4-limb wire indices; base_offset = 0, capacity = 2^20. -/
  | imtGet (key : Expr)
  | imtContains (key : Expr)
  | imtSet (key value : Expr)
  /-- IMT external / other-user reads (software simulate key-addressed). -/
  | imtGetExternal (contractId key : Expr)
  | imtGetOther (userId contractId key : Expr)
  | imtContainsOther (userId contractId key : Expr)
  /-- Felt-valued conditional used to materialize carry/borrow without field
      division. `condition` is Bool; both branches are Felt expressions. -/
  | select (condition thenValue elseValue : Expr)
  /-- G5-WIDE: result limb `limbIndex` of a target-owned `bindWideUintMul`.
      Must appear in the same lexical statement region as the binding. -/
  | wideUintMulLimb (bitWidth operationId limbIndex : Nat)
  /-- G5-WIDE: result limb `limbIndex` of a `bindWideUintDivMod`. -/
  | wideUintDivModLimb (resultKind : WideUInt128DivModResultV1)
      (bitWidth operationId limbIndex : Nat)
  /-- G5-WIDE: result limb `limbIndex` of a `bindWideUintShift`. -/
  | wideUintShiftLimb (kind : WideUInt128ShiftKindV1)
      (bitWidth operationId limbIndex : Nat)
  deriving BEq, Inhabited, Repr

inductive Statement where
  | store (fieldIndex : Nat) (value : Expr)
  | assert (condition : Expr)
  | assertWithMessage (condition : Expr) (message : String)
  | returnValue (value : Expr)
  /-- Multi-value return (B-RET-ABI): 2..8 Felt leaves packed as one Psy
      `[Felt; N]` return value. -/
  | returnAggregate (values : Array Expr)
  | returnNone
  | ifThenElse (condition : Expr) (thenBody elseBody : Array Statement)
  /-- Bounded `for` static unroll (PSY-LOOP): `maxIterations` guarded steps
      of `body` with the loop variable bound to `start + k`. -/
  | forLoop (start endExclusive : Expr) (maxIterations : Nat) (body : Array Statement)
  /-- DPN event record (DPN-6): identity context is circuit-side; the
      declared event `name` is source metadata only. -/
  | emitEvent (name : String) (args : Array Expr)
  /-- Void synchronous external call (DPN-6 PARTIAL): hashed static
      qualified name, `numOutputs = 0`, no response binding. -/
  | externalCall (callee : Array String) (args : Array Expr)
  /-- G5-WIDE: target-owned schoolbook mul binding. `lhs`/`rhs` are
      `limbCount` UInt32 limbs; `operationId` scopes the `wideUintMulLimb`
      result references. -/
  | bindWideUintMul (bitWidth operationId : Nat) (lhs rhs : Array Expr)
  /-- G5-WIDE: target-owned restoring div/mod binding (unrolled). -/
  | bindWideUintDivMod (resultKind : WideUInt128DivModResultV1)
      (bitWidth operationId : Nat) (lhs rhs : Array Expr)
  /-- G5-WIDE: target-owned exact shift binding (fixed bit-width bit walk). -/
  | bindWideUintShift (kind : WideUInt128ShiftKindV1)
      (bitWidth operationId : Nat) (value : Array Expr) (count : Expr)
  deriving BEq, Inhabited, Repr



inductive FunctionKind where
  | initialize
  | mutate
  deriving BEq, Inhabited, Repr, DecidableEq

structure PlanParam where
  sourceIndex : Nat
  name : String
  isBool : Bool
  deriving BEq, Inhabited, Repr

structure PlanFunction where
  index : Nat
  name : String
  kind : FunctionKind
  params : Array PlanParam
  body : Array Statement
  resultIsBool : Bool
  resultIsUnit : Bool
  deriving BEq, Inhabited, Repr

/-- Target-owned Psy Plan. Carries the artifact program name and the logical
    state leaf order; DPN physical leaf index = declaration index. -/
structure Plan where
  programName : String
  stateFieldNames : Array String
  functions : Array PlanFunction
  /-- Error constructor names collected from `errorNamed` terminals.
      Diagnostic metadata only — DPN circuits trap via assertions. -/
  errors : Array String := #[]

private def joinRepr (args : Array Expr) : String :=
  String.intercalate " " ((args.map (fun a => toString (repr a))).toList)

private def renderCallee (callee : Array String) : String :=
  String.intercalate "." callee.toList

/-- Stable low-tech canonical rendering for registry digests. Not a JSON
    round-trip: purely a fingerprint of the Plan content. -/
private partial def renderExpr : Expr → String
  | .literal v => s!"lit {v}"
  | .boolLiteral v => s!"b {v}"
  | .param i => s!"p {i}"
  | .stateLoad i => s!"slot {i}"
  | .checkedAdd l r => s!"(+ {renderExpr l} {renderExpr r})"
  | .checkedSub l r => s!"(- {renderExpr l} {renderExpr r})"
  | .checkedMul l r => s!"(* {renderExpr l} {renderExpr r})"
  | .checkedDiv l r => s!"(/ {renderExpr l} {renderExpr r})"
  | .checkedMod l r => s!"(% {renderExpr l} {renderExpr r})"
  | .compare op l r =>
      let op := match op with
        | .lt => "<" | .le => "<=" | .eq => "==" | .ne => "!=" | .ge => ">=" | .gt => ">"
      s!"({op} {renderExpr l} {renderExpr r})"
  | .bitAnd l r => s!"(& {renderExpr l} {renderExpr r})"
  | .bitOr l r => s!"(| {renderExpr l} {renderExpr r})"
  | .bitXor l r => s!"(^ {renderExpr l} {renderExpr r})"
  | .boolNot v => s!"(! {renderExpr v})"
  | .select c t e => s!"(sel {renderExpr c} {renderExpr t} {renderExpr e})"
  | .shl l r => s!"(<< {renderExpr l} {renderExpr r})"
  | .shr l r => s!"(>> {renderExpr l} {renderExpr r})"
  | .checkedBitNot v => s!"(bnot {renderExpr v})"
  | .ctxUserId => "ctx userId"
  | .ctxContractId => "ctx contractId"
  | .ctxCheckpointId => "ctx checkpointId"
  | .ctxNonce => "ctx nonce"
  | .ctxCallerContractId => "ctx callerContractId"
  | .ctxUserPublicKeyHash => "ctx userPublicKeyHash"
  | .ctxSessionProofTreeRoot => "ctx sessionProofTreeRoot"
  | .hashNoPad args => s!"(hashNoPad {joinRepr args})"
  | .hashPad args => s!"(hashPad {joinRepr args})"
  | .hashTwoToOne args => s!"(hash2to1 {joinRepr args})"
  | .keccak256 args => s!"(keccak {joinRepr args})"
  | .hashOutLimb kind i args => s!"(hashOut {kind} {i} {joinRepr args})"
  | .imtGet k => s!"(imtGet {repr k})"
  | .imtContains k => s!"(imtHas {repr k})"
  | .imtSet k v => s!"(imtSet {repr k} {repr v})"
  | .imtGetExternal c k => s!"(imtGetExt {repr c} {repr k})"
  | .imtGetOther u c k => s!"(imtGetOther {repr u} {repr c} {repr k})"
  | .imtContainsOther u c k => s!"(imtHasOther {repr u} {repr c} {repr k})"
  | .wideUintMulLimb bw op li => s!"(wmul {bw} {op} {li})"
  | .wideUintDivModLimb kind bw op li =>
      let k := match kind with | .quotient => "q" | .remainder => "r"
      s!"(wdiv {k} {bw} {op} {li})"
  | .wideUintShiftLimb kind bw op li =>
      let k := match kind with | .shl => "shl" | .shr => "shr"
      s!"(wshl {k} {bw} {op} {li})"

private partial def renderStmts (indent : String) (stmts : Array Statement) : String :=
  let openBrace : String := "{"
  let closeBrace : String := "}"
  let nl : String := "\n"
  let one : Statement → String := fun stmt =>
    match stmt with
    | .store i v => s!"{indent}slot {i} := {renderExpr v}{nl}"
    | .assert c => s!"{indent}assert {renderExpr c}{nl}"
    | .assertWithMessage c m => s!"{indent}assert {renderExpr c} : {m}{nl}"
    | .returnValue v => s!"{indent}ret {renderExpr v}{nl}"
    | .returnAggregate vs =>
        s!"{indent}ret [{String.intercalate ", " ((vs.map renderExpr).toList)}]{nl}"
    | .returnNone => s!"{indent}ret{nl}"
    | .ifThenElse c thn els =>
        let thnText := renderStmts (indent ++ "  ") thn
        let elsText := renderStmts (indent ++ "  ") els
        let condText : String := renderExpr c
        String.intercalate "" [
          indent, "if ", condText, " ", openBrace, nl, thnText,
          indent, closeBrace, " else ", openBrace, nl, elsText,
          indent, closeBrace, nl]
    | .forLoop s e n body =>
        let bodyText := renderStmts (indent ++ "  ") body
        String.intercalate "" [
          indent, "for ", renderExpr s, " ..< ", renderExpr e,
          " bounded ", toString n, " ", openBrace, nl, bodyText,
          indent, closeBrace, nl]
    | .emitEvent name args =>
        s!"{indent}emit {name}({joinRepr args}){nl}"
    | .externalCall callee args =>
        s!"{indent}call {renderCallee callee}({joinRepr args}){nl}"
    | .bindWideUintMul bw op lhs rhs =>
        s!"{indent}wbind mul {bw} {op} {joinRepr lhs} {joinRepr rhs}{nl}"
    | .bindWideUintDivMod kind bw op lhs rhs =>
        let k := match kind with | .quotient => "q" | .remainder => "r"
        s!"{indent}wbind div {k} {bw} {op} {joinRepr lhs} {joinRepr rhs}{nl}"
    | .bindWideUintShift kind bw op value count =>
        let k := match kind with | .shl => "shl" | .shr => "shr"
        s!"{indent}wbind {k} {bw} {op} {joinRepr value} {renderExpr count}{nl}"
  String.intercalate "" (stmts.map one).toList

def renderCanonical (plan : Plan) : String :=
  let fns :=
    plan.functions.qsort (·.name < ·.name)
  let fnText :=
    fns.map fun fn =>
      let params := fn.params.map (fun p => s!"p{p.sourceIndex}{if p.isBool then "b" else ""}")
      let kind := match fn.kind with
        | .initialize => "init"
        | .mutate => "mut"
      let ret := if fn.resultIsUnit then "unit" else if fn.resultIsBool then "bool" else "u64"
      s!"fn {fn.name}:{kind}({String.intercalate "," params.toList}) r={ret}\n" ++
      renderStmts "  " fn.body
  (s!"psy {plan.programName} | " ++
    String.intercalate "," plan.stateFieldNames.toList ++
    (if plan.errors.isEmpty then "" else
      " | errors " ++ String.intercalate "," plan.errors.toList) ++ "\n") ++
    String.intercalate "" fnText.toList

end ProofForge.Psy.Plan

