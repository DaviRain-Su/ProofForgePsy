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
/-- Max guarded static-unroll steps for PSY-LOOP (mirrors the DPN lowerer). -/
private def maxUnrollBudget : Nat := 64

/-- Count expression nodes with a hard depth budget; `none` = over budget. -/
private def validateExprNodes (expr : Expr) : Option Nat :=
  match expr with
  | .literal _ | .boolLiteral _ | .param _ | .stateLoad _
  | .ctxUserId | .ctxContractId | .ctxCheckpointId | .ctxNonce
  | .ctxCallerContractId | .ctxUserPublicKeyHash | .ctxSessionProofTreeRoot
  | .wideUintMulLimb _ _ _ | .wideUintDivModLimb _ _ _ _
  | .wideUintShiftLimb _ _ _ _ => some 1
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
  | .hashNoPad args | .hashPad args | .hashTwoToOne args | .keccak256 args =>
      args.foldl (init := some 1) fun acc a =>
        match acc, validateExprNodes a with
        | some n, some d =>
            if n + d > maxExprDepth then none else some (n + d)
        | _, _ => none
  | .hashOutLimb kind limbIndex args =>
      if kind > 5 || limbIndex ≥ 4 then none
      else
        args.foldl (init := some 1) fun acc a =>
          match acc, validateExprNodes a with
          | some n, some d =>
              if n + d > maxExprDepth then none else some (n + d)
          | _, _ => none
  | .imtGet k | .imtContains k => do
      let d ← validateExprNodes k
      if d + 1 > maxExprDepth then none else some (d + 1)
  | .imtSet k v => do
      let dk ← validateExprNodes k
      let dv ← validateExprNodes v
      if dk + dv + 1 > maxExprDepth then none else some (dk + dv + 1)
  | .imtGetExternal c k => do
      let dc ← validateExprNodes c
      let dk ← validateExprNodes k
      if dc + dk + 1 > maxExprDepth then none else some (dc + dk + 1)
  | .imtGetOther u c k | .imtContainsOther u c k => do
      let du ← validateExprNodes u
      let dc ← validateExprNodes c
      let dk ← validateExprNodes k
      if du + dc + dk + 1 > maxExprDepth then none else some (du + dc + dk + 1)

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
    | .returnAggregate values =>
        if values.isEmpty || values.size > 8 then
          planError "aggregate return arity must be 1..8"
        for v in values do validateExpr v
    | .assert condition | .assertWithMessage condition _ =>
        validateExpr condition
    | .returnNone => pure ()
    | .ifThenElse condition thenBody elseBody =>
        validateExpr condition
        validateStatements thenBody
        validateStatements elseBody
    | .forLoop start endExclusive maxIter body =>
        validateExpr start
        validateExpr endExclusive
        if maxIter > maxUnrollBudget then
          planError s!"for loop unroll budget {maxIter} exceeds {maxUnrollBudget}"
        validateStatements body
    | .emitEvent _ args =>
        for a in args do validateExpr a
    | .externalCall callee args =>
        if callee.size < 2 then
          planError "external callee must have ≥2 qualified-name components"
        for a in args do validateExpr a
    | .bindWideUintMul _ _ lhs rhs =>
        for l in lhs do validateExpr l
        for r in rhs do validateExpr r
    | .bindWideUintDivMod _ _ _ lhs rhs =>
        for l in lhs do validateExpr l
        for r in rhs do validateExpr r
    | .bindWideUintShift _ _ _ value count =>
        for v in value do validateExpr v
        validateExpr count

/-- Does any statement in this sequence return a value (possibly under a branch)? -/
private partial def returnsAnywhere (stmts : Array Statement) : Bool :=
  stmts.any fun
    | .returnValue _ => true
    | .returnAggregate _ => true
    | .ifThenElse _ t e => returnsAnywhere t || returnsAnywhere e
    | _ => false

/-- A lone trap arm (`assertWithMessage false "revert[:name]"`) traps before
    any later return, so it counts as a returning path for arity purposes. -/
private def isLoneTrapArm : Array Statement → Bool
  | #[.assertWithMessage (.boolLiteral false) msg] =>
      msg == "revert" || msg.startsWith "revert:"
  | _ => false


/-- Return-form consistency: a branch that returns must be matched by the
    other arm (the DPN lowerer merges returns through `Select` and rejects
    asymmetric arms with a worse error otherwise). -/
private partial def checkReturnForms (stmts : Array Statement) : Except String Unit := do
  for stmt in stmts do
    match stmt with
    | .ifThenElse _ thenBody elseBody =>
        let thnReturns := returnsAnywhere thenBody || isLoneTrapArm thenBody
        let elsReturns := returnsAnywhere elseBody || isLoneTrapArm elseBody
        if thnReturns != elsReturns then
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
