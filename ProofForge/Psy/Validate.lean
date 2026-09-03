import ProofForge.Psy.Plan

/-!
# Psy Plan validation (psy-dpn-v1 slice)

Trimmed port of `ProofForgeV2.Targets.Psy.ValidatePlanV1`. What survives the
cut: function/parameter/statement limits and the expression depth budget.
Wide-binding inventories, aggregate return forms, event/call payload rules,
and `hashOutLimb` checks are all gone with the constructors they guarded.
-/

namespace ProofForge.Psy.Plan.Validate

private def planError (message : String) : Except String α :=
  .error s!"psy/plan: {message}"

private def maxFunctions : Nat := 256
private def maxParams : Nat := 64
private def maxBodyStatements : Nat := 4096
private def maxExprDepth : Nat := 256

/-- Count expression nodes with a hard depth budget; `none` = over budget. -/
private def validateExprNodes (expr : Expr) : Option Nat :=
  match expr with
  | .literal _ | .boolLiteral _ | .param _ | .stateLoad _
  | .ctxUserId | .ctxContractId | .ctxCheckpointId | .ctxNonce
  | .ctxCallerContractId | .ctxUserPublicKeyHash | .ctxSessionProofTreeRoot => some 1
  | .checkedAdd l r | .checkedSub l r | .checkedMul l r | .checkedDiv l r
  | .checkedMod l r | .bitAnd l r | .bitOr l r | .bitXor l r
  | .shl l r | .shr l r => do
      let dl ← validateExprNodes l
      let dr ← validateExprNodes r
      if dl + dr + 1 > maxExprDepth then none else some (dl + dr + 1)
  | .compare _ l r => do
      let dl ← validateExprNodes l
      let dr ← validateExprNodes r
      if dl + dr + 1 > maxExprDepth then none else some (dl + dr + 1)
  | .boolNot o | .checkedBitNot o => do
      let d ← validateExprNodes o
      if d + 1 > maxExprDepth then none else some (d + 1)
  | .select c t e => do
      let dc ← validateExprNodes c
      let dt ← validateExprNodes t
      let de ← validateExprNodes e
      if dc + dt + de + 1 > maxExprDepth then none else some (dc + dt + de + 1)

private def validateExpr (expr : Expr) : Except String Unit :=
  match validateExprNodes expr with
  | some _ => .ok ()
  | none => planError "expression exceeds the depth/node limit"

private partial def validateStatements (stmts : Array Statement) : Except String Unit := do
  if stmts.size > maxBodyStatements then
    planError "function body exceeds the statement limit"
  for stmt in stmts do
    match stmt with
    | .store _ value | .returnValue value =>
        validateExpr value
    | .assert condition | .assertWithMessage condition _ =>
        validateExpr condition
    | .returnNone => pure ()
    | .ifThenElse condition thenBody elseBody =>
        validateExpr condition
        validateStatements thenBody
        validateStatements elseBody

/-- Does any statement in this sequence return a value (possibly under a branch)? -/
private partial def returnsAnywhere (stmts : Array Statement) : Bool :=
  stmts.any fun
    | .returnValue _ => true
    | .ifThenElse _ t e => returnsAnywhere t || returnsAnywhere e
    | _ => false

/-- Return-form consistency: a branch that returns must be matched by the
    other arm (the DPN lowerer merges returns through `Select` and rejects
    asymmetric arms with a worse error otherwise). -/
private partial def checkReturnForms (stmts : Array Statement) : Except String Unit := do
  for stmt in stmts do
    match stmt with
    | .ifThenElse _ thenBody elseBody =>
        if returnsAnywhere thenBody != returnsAnywhere elseBody then
          planError "if arms must both return or neither"
        checkReturnForms thenBody
        checkReturnForms elseBody
    | _ => pure ()

def validatePlan (plan : Plan) : Except String Unit := do
  if plan.functions.isEmpty then
    planError "plan has no functions"
  if plan.functions.size > maxFunctions then
    planError "plan exceeds the function limit"
  if plan.stateFieldNames.isEmpty then
    planError "plan has no state fields"
  for fn in plan.functions do
    if fn.params.size > maxParams then
      planError s!"{fn.name} exceeds the parameter limit"
    validateStatements fn.body
    checkReturnForms fn.body

end ProofForge.Psy.Plan.Validate
