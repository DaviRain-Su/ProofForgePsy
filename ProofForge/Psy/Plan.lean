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
  | select (condition thenValue elseValue : Expr)
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
  deriving BEq, Inhabited, Repr

inductive Statement where
  | store (fieldIndex : Nat) (value : Expr)
  | assert (condition : Expr)
  | assertWithMessage (condition : Expr) (message : String)
  | returnValue (value : Expr)
  | returnNone
  | ifThenElse (condition : Expr) (thenBody elseBody : Array Statement)
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
    | .returnNone => s!"{indent}ret{nl}"
    | .ifThenElse c thn els =>
        let thnText := renderStmts (indent ++ "  ") thn
        let elsText := renderStmts (indent ++ "  ") els
        let condText : String := renderExpr c
        String.intercalate "" [
          indent, "if ", condText, " ", openBrace, nl, thnText,
          indent, closeBrace, " else ", openBrace, nl, elsText,
          indent, closeBrace, nl]
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

