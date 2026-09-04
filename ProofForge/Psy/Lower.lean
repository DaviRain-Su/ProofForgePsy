/-
  Psy target lowering boundary: extracted Core IR → Psy Plan.

  This is the fork counterpart of `ProofForge.Evm.IR.fromExtracted`: project
  the extractor dialect into the Psy dialect (trivially — Psy owns no effect
  extensions), then translate the target-neutral Core ops into the
  target-owned `Psy.Plan` statement language that `Psy.Dpn.Lower` consumes.

  Canonical extractor shapes relied on (verified against Examples):
  * init: one `returnState v` per state leaf, in declaration order.
  * view: scalar expression terminated by `returnU64 v`; branches return in
    both arms.
  * mutate (guard-folded): `[checkedXU64 l r, okState _, errorTerminal]` —
    the checked op's own trap covers the error tail (dropped, mirroring the
    V2 checked-assert convention).
  * mutate (explicit stores): `[storeField …, okState v]` per branch;
    `ite … thn [errorTerminal]` is the guard shape. The error arm becomes a
    gated `assertWithMessage false "revert"` (DPN trap = proof failure), plus
    a dead `returnValue (lit 0)` when the other arm returns, so return arity
    stays symmetric.

  Admitted (PSY-LOOP): bounded `forAccum`/`forBody` static unroll (≤64
  steps) with the loop variable substituted to per-step literals, including
  loop-var addends (`acc += i.toUInt64`).

  Fail-closed boundaries (psy-dpn-v1 slice): dynamic vector indices, returns
  inside loop bodies, typed error payloads (zero-arg named reverts are
  tagged per PSY-TYPED-ERROR), aggregate (struct) parameters, whole-state
  scalar reads, wide (UInt128/256) state slots, >64-step loops.
-/
import ProofForge.Extract.IR
import ProofForge.Core.Target
import ProofForge.Psy.Ops
import ProofForge.Psy.Plan
import ProofForge.Psy.Validate

namespace ProofForge.Psy.Lower

open ProofForge.Psy.Plan

private def lowerError (message : String) : Except String α :=
  .error s!"psy/lower: {message}"

/--
Registration of the extractor-to-Psy projection. The extractor dialect wraps
target leaves (`ValKind.psy kind`); the projection unwraps Psy leaves and
rejects every other intrinsic (this slice admits no other context reads).

The lowering consumes the projected methods re-wrapped in the extractor
aliases (`wrapVal`/`wrapOp`) so one recursive translation serves both the
extractor's combined dialect and any future psy-only dialect.
-/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt
      Psy.Ops.ValKind Psy.Ops.OpExt where
  name := "Psy"
  projectValExt := fun
    | .psy kind => pure kind
  projectOpExt := fun _ payload =>
    match payload with
    | .psy p =>
        p.elim (motive := fun _ =>
          Except String (Psy.Ops.OpExt (Core.Ops.Val Psy.Ops.ValKind)))
  valArity := Psy.Ops.ValKind.arity
  -- Hash/IMT leaves carry their arguments as operands; arity is the MAXIMUM
  -- (the extractor flattens `Array UInt64` literals into individual operands).
  valArityAllows := fun kind n => n <= Psy.Ops.ValKind.arity kind
  opWellFormed := Psy.Ops.Op.wellFormed
  cfgDialect := {
    mapValues := fun _ payload =>
      payload.elim (motive := fun _ => Psy.Ops.OpExt (Core.Ops.Val Psy.Ops.ValKind))
    values := fun payload =>
      payload.elim (motive := fun _ => Array (Core.Ops.Val Psy.Ops.ValKind))
    payloadEq := fun left _ =>
      left.elim (motive := fun _ => Bool)
  }

abbrev SrcVal := Extract.IR.Val
abbrev SrcOp := Extract.IR.Op

/-- Re-wrap a projected Core value into the extractor dialect alias. -/
private def wrapVal : Psy.Ops.Val → SrcVal
  | .arg i => .arg i
  | .local i => .local i
  | .lit n => .lit n
  | .field base name => .field (wrapVal base) name
  | .select c l r t e => .select c (wrapVal l) (wrapVal r) (wrapVal t) (wrapVal e)
  | .addU64 l r => .addU64 (wrapVal l) (wrapVal r)
  | .subU64 l r => .subU64 (wrapVal l) (wrapVal r)
  | .mulU64 l r => .mulU64 (wrapVal l) (wrapVal r)
  | .divU64 l r => .divU64 (wrapVal l) (wrapVal r)
  | .modU64 l r => .modU64 (wrapVal l) (wrapVal r)
  | .bitAnd l r => .bitAnd (wrapVal l) (wrapVal r)
  | .bitOr l r => .bitOr (wrapVal l) (wrapVal r)
  | .bitXor l r => .bitXor (wrapVal l) (wrapVal r)
  | .bitNot v => .bitNot (wrapVal v)
  | .shiftL l r => .shiftL (wrapVal l) (wrapVal r)
  | .shiftR l r => .shiftR (wrapVal l) (wrapVal r)
  | .indexGet b n i len off => .indexGet (wrapVal b) n (wrapVal i) len off
  | .loopIx => .loopIx
  | .ext kind operands => .ext (.psy kind) (operands.map wrapVal)

/-- Re-wrap projected Core ops into the extractor dialect alias. -/
private partial def wrapOp : ProofForge.Core.Ops.Op Psy.Ops.ValKind Psy.Ops.OpExt → SrcOp
  | .letLocal i v => .letLocal i (wrapVal v)
  | .setLocal i v => .setLocal i (wrapVal v)
  | .joinLocal i => .joinLocal i
  | .checkedAddU64 l r => .checkedAddU64 (wrapVal l) (wrapVal r)
  | .checkedSubU64 l r => .checkedSubU64 (wrapVal l) (wrapVal r)
  | .checkedMulU64 l r => .checkedMulU64 (wrapVal l) (wrapVal r)
  | .checkedDivU64 l r => .checkedDivU64 (wrapVal l) (wrapVal r)
  | .checkedModU64 l r => .checkedModU64 (wrapVal l) (wrapVal r)
  | .ite c l r thn els => .ite c (wrapVal l) (wrapVal r) (wrapOps thn) (wrapOps els)
  | .forAccum n v i => .forAccum n (wrapVal v) i
  | .forBody n body => .forBody n (wrapOps body)
  | .indexSetLeaf n i v len leaf => .indexSetLeaf n (wrapVal i) (wrapVal v) len leaf
  | .indexSet n i v len off => .indexSet n (wrapVal i) (wrapVal v) len off
  | .storeField n v => .storeField n (wrapVal v)
  | .okState v => .okState (wrapVal v)
  | .errorOverflow => .errorOverflow
  | .errorNamed n => .errorNamed n
  | .emitEvent name payload => .emitEvent name (wrapVal payload)
  | .externalCall callee args => .externalCall callee (args.map wrapVal)
  | .errorTyped frame => .errorTyped (frame.mapValues wrapVal)
  | .returnU64 v => .returnU64 (wrapVal v)
  | .returnState v => .returnState (wrapVal v)
  | .ext payload =>
      -- Psy owns no OpExt payloads: the projection strips the extension, so
      -- the re-wrap cannot see one either. `elim` needs its motive spelled
      -- out for the type directors on both sides.
      Core.Ops.Op.ext (Extract.IR.OpExt.psy
        (payload.elim (motive := fun _ => Psy.Ops.OpExt (Core.Ops.Val Extract.IR.ValKind))))
where
  wrapOps : Array (ProofForge.Core.Ops.Op Psy.Ops.ValKind Psy.Ops.OpExt) → Array SrcOp :=
    Array.map wrapOp

/-- Per-method lowering context. -/
structure Ctx where
  /-- State leaf name → physical leaf index (declaration order). -/
  leafIndexOf : String → Option Nat
  /-- Fixed vector name → (base leaf index, leaves per element). -/
  vectorOf : String → Option (Nat × Nat)
  paramCount : Nat
  /-- Init args are all parameters; other kinds take the state at `arg paramCount`. -/
  isInit : Bool
  /-- Public scalar result count (0 = unit). -/
  retCount : Nat

/-- Local lexical environment: extractor local index → Plan expression. -/
abbrev LocalEnv := Array (Nat × Expr)

private def envLookup (env : LocalEnv) (i : Nat) : Except String Expr :=
  match env.find? (·.1 == i) with
  | some (_, e) => pure e
  | none => lowerError s!"unbound local {i}"

/-- Translate one target-neutral scalar value into a Plan expression. -/
partial def valToExpr (ctx : Ctx) (env : LocalEnv) : SrcVal → Except String Expr
  | .lit n => pure (.literal n)
  | .arg i =>
      if !ctx.isInit && i == ctx.paramCount then
        lowerError "whole-state value is not a scalar (project a field)"
      else if i < ctx.paramCount then
        pure (.param i)
      else
        lowerError s!"arg {i} out of range (paramCount {ctx.paramCount})"
  | .field (.arg i) name =>
      if !ctx.isInit && i == ctx.paramCount then
        match ctx.leafIndexOf name with
        | some idx => pure (.stateLoad idx)
        | none => lowerError s!"unknown state leaf {name}"
      else if i < ctx.paramCount then
        lowerError s!"aggregate parameter projection p{i}.{name} is not admitted \
          (psy-dpn-v1 parameters are scalars)"
      else
        lowerError s!"arg {i} out of range (paramCount {ctx.paramCount})"
  | .field (.local i) _ => do
      -- A projection off a local is unreachable for scalar locals; surface the binding.
      let _ ← envLookup env i
      lowerError s!"nested field projection off local {i} is not admitted"
  | .field base _ => do
      let _ ← valToExpr ctx env base
      lowerError "nested field projection is not admitted in psy-dpn-v1"
  | .local i => envLookup env i
  | .loopIx =>
      lowerError "loop variable reached the Psy boundary (state loops fail closed in psy-dpn-v1)"
  | .select c l r t e => do
      let lw ← valToExpr ctx env l
      let rw ← valToExpr ctx env r
      let tw ← valToExpr ctx env t
      let ew ← valToExpr ctx env e
      pure (.select (.compare c lw rw) tw ew)
  -- Plain Lean UInt64 arithmetic is wrapping; Psy has no faithful wrapping
  -- Felt interpretation, so every arithmetic node is checked (trap on overflow).
  | .addU64 l r => return .checkedAdd (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .subU64 l r => return .checkedSub (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .mulU64 l r => return .checkedMul (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .divU64 l r => return .checkedDiv (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .modU64 l r => return .checkedMod (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .bitAnd l r => return .bitAnd (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .bitOr l r => return .bitOr (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .bitXor l r => return .bitXor (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .bitNot v => return .checkedBitNot (← valToExpr ctx env v)
  | .shiftL l r => return .shl (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .shiftR l r => return .shr (← valToExpr ctx env l) (← valToExpr ctx env r)
  | .indexGet _ name idx _ elemOff => do
      -- Vector reads with a dynamic index are not admitted: DPN state slots are static.
      let some base := ctx.vectorOf name
        | lowerError s!"unknown vector {name}"
      let (baseLeaf, elementLeaves) := base
      let some k := (match idx with | .lit n => some n.toNat | _ => none)
        | lowerError s!"dynamic index into vector {name} (DPN state slots are static)"
      unless elemOff % 8 == 0 do
        lowerError s!"vector {name} leaf byte offset {elemOff} is not limb-aligned"
      pure (.stateLoad (baseLeaf + k * elementLeaves + elemOff / 8))
  | .ext (.psy kind) operands => do
      -- Context leaves are nullary; SDK leaves carry their decoded arguments
      -- (up to the kind's maximum arity — Array literals flatten).
      unless operands.size <= Psy.Ops.ValKind.arity kind do
        return ← lowerError s!"psy SDK leaf {repr kind} expects at most {Psy.Ops.ValKind.arity kind} operands, got {operands.size}"
      let oe ← operands.mapM (valToExpr ctx env)
      let atIdx (i : Nat) : Expr := oe.getD i (.literal 0)
      pure (match kind with
        | .ctxUserId => .ctxUserId
        | .ctxContractId => .ctxContractId
        | .ctxCheckpointId => .ctxCheckpointId
        | .ctxNonce => .ctxNonce
        | .ctxCallerContractId => .ctxCallerContractId
        | .ctxUserPublicKeyHash => .ctxUserPublicKeyHash
        | .ctxSessionProofTreeRoot => .ctxSessionProofTreeRoot
        | .psyEvent => .boolLiteral true  -- effects carry no value
        | .cryptoHashNoPad => .hashNoPad oe
        | .cryptoHashPad => .hashPad oe
        | .cryptoHashTwoToOne => .hashTwoToOne oe
        | .cryptoKeccak256 => .keccak256 oe
        | .cryptoHashNoPadLimb =>
            -- Last operand is the limb index literal; the rest are the args.
            match oe.back? with
            | some (.literal limb) =>
                .hashOutLimb 0 limb.toNat (oe.extract 0 (oe.size - 1))
            | _ => .hashOutLimb 0 0 (oe.extract 0 (oe.size - 1))
        | .cryptoHashTwoToOneLimb =>
            match oe.back? with
            | some (.literal limb) =>
                .hashOutLimb 2 limb.toNat (oe.extract 0 (oe.size - 1))
            | _ => .hashOutLimb 2 0 (oe.extract 0 (oe.size - 1))
        | .imtGet => .imtGet (atIdx 0)
        | .imtContains => .imtContains (atIdx 0)
        | .imtSet => .imtSet (atIdx 0) (atIdx 1)
        | .imtGetExternal => .imtGetExternal (atIdx 0) (atIdx 1)
        | .imtGetOther => .imtGetOther (atIdx 0) (atIdx 1) (atIdx 2)
        | .imtContainsOther => .imtContainsOther (atIdx 0) (atIdx 1) (atIdx 2))


private def isErrorTerminal : SrcOp → Bool
  | .errorOverflow | .errorNamed _ => true
  | _ => false

/-- Does this sequence end in an error terminal with a checked op before it?
    That tail is the guard-folded Except shape; the checked op's DPN trap
    assertion subsumes it. -/
private def foldableErrorTail (ops : Array SrcOp) : Bool :=
  (ops.back?.any isErrorTerminal) &&
    ops.any fun
      | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
      | .checkedDivU64 .. | .checkedModU64 .. => true
      | _ => false

/-- Max static unroll steps for the Core→Plan boundary (PSY-LOOP budget;
    the DPN lowerer enforces the same budget again). -/
private def maxUnrollSteps : Nat := 64

/-- Replace `.loopIx` with the literal loop index `k` during unrolling. -/
private partial def substituteLoopIx (v : Expr) (k : Option Nat) : Expr :=
  let _ := k
  v  -- loopIx never appears in accumulator addends (checked at valToExpr)

/-- Unroll an accumulator chain: `acc0 op addend` nested `n` deep. -/
private def unrollAccum (acc : Expr) (addend : Expr) (n : Nat) : Expr :=
  match n with
  | 0 => acc
  | n' + 1 => unrollAccum (.checkedAdd acc addend) addend n'

private partial def substituteLoopIxVal (v : SrcVal) (k : Nat) : SrcVal :=
  match v with
  | .loopIx => .lit (UInt64.ofNat k)
  | .field base name => .field (substituteLoopIxVal base k) name
  | .bitAnd l r => .bitAnd (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .bitOr l r => .bitOr (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .bitXor l r => .bitXor (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .bitNot v => .bitNot (substituteLoopIxVal v k)
  | .shiftL l r => .shiftL (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .shiftR l r => .shiftR (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .addU64 l r => .addU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .subU64 l r => .subU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .mulU64 l r => .mulU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .divU64 l r => .divU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .modU64 l r => .modU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
  | .indexGet base name i len off =>
      .indexGet (substituteLoopIxVal base k) name (substituteLoopIxVal i k) len off
  | .select c l r t e =>
      .select c (substituteLoopIxVal l k) (substituteLoopIxVal r k)
        (substituteLoopIxVal t k) (substituteLoopIxVal e k)
  | .ext kind operands => .ext kind (operands.map (substituteLoopIxVal · k))
  | other => other

/-- Substitute the literal loop index into every op of an unrolled body. -/
private partial def substituteLoopIxOps (ops : Array SrcOp) (k : Nat) :
    Array SrcOp :=
  ops.map fun op =>
    match op with
    | .letLocal i v => .letLocal i (substituteLoopIxVal v k)
    | .setLocal i v => .setLocal i (substituteLoopIxVal v k)
    | .checkedAddU64 l r => .checkedAddU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
    | .checkedSubU64 l r => .checkedSubU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
    | .checkedMulU64 l r => .checkedMulU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
    | .checkedDivU64 l r => .checkedDivU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
    | .checkedModU64 l r => .checkedModU64 (substituteLoopIxVal l k) (substituteLoopIxVal r k)
    | .storeField name v => .storeField name (substituteLoopIxVal v k)
    | .indexSet name i v len off =>
        .indexSet name (substituteLoopIxVal i k) (substituteLoopIxVal v k) len off
    | .indexSetLeaf name i v len leaf =>
        .indexSetLeaf name (substituteLoopIxVal i k) (substituteLoopIxVal v k) len leaf
    | .okState v => .okState (substituteLoopIxVal v k)
    | .returnU64 v => .returnU64 (substituteLoopIxVal v k)
    | .ite c l r thn els =>
        .ite c (substituteLoopIxVal l k) (substituteLoopIxVal r k)
          (substituteLoopIxOps thn k) (substituteLoopIxOps els k)
    | .forAccum n v i => .forAccum n (substituteLoopIxVal v k) i
    | .forBody n body => .forBody n (substituteLoopIxOps body k)
    | other => other

/-- Implicit `okState` destination, mirroring `Core.Eval.implicitDestination`:
    a known field name wins; otherwise the first state leaf. -/
private def implicitDestLeaf (ctx : Ctx) (v : SrcVal) : Nat :=
  match v with
  | .field _ name => (ctx.leafIndexOf name).getD 0
  | _ => 0

/-- Translator state: local environment + the pending checked-arithmetic result
    of the current sequence (consumed by `okState`, mirroring `Core.Eval`'s
    implicit-destination convention). -/
private structure SeqState where
  env : LocalEnv := #[]
  pending : Option Expr := none
  /-- Whether the current sequence already stored one leaf explicitly. -/
  sawStore : Bool := false
  /-- A value return already terminated this sequence. -/
  returned : Bool := false
  deriving Inhabited

/-- A lone trap arm: one gated `assertWithMessage false "revert[:name]"`
    (the PSY-TYPED-ERROR zero-arg revert tags the constructor name). -/
private def isLoneTrap : Array Statement → Bool
  | #[.assertWithMessage (.boolLiteral false) msg] => msg == "revert" || msg.startsWith "revert:"
  | _ => false

/-- Balance guard-style branches: when exactly one arm is a lone trap and the
    other returns, give the trap arm a dead `returnValue 0` so DPN return
    arity stays symmetric (the trap fires first at proof time). -/
private partial def returnsAnywhereDeep (stmts : Array Statement) : Bool :=
  stmts.any fun
    | .returnValue _ => true
    | .ifThenElse _ t e => returnsAnywhereDeep t || returnsAnywhereDeep e
    | _ => false

private def balanceTrapArms (thn els : Array Statement) :
    Array Statement × Array Statement :=
  match isLoneTrap thn, isLoneTrap els with
  | true, false =>
      if returnsAnywhereDeep els then
        (thn.push (.returnValue (.literal 0)), els)
      else (thn, els)
  | false, true =>
      if returnsAnywhereDeep thn then
        (thn, els.push (.returnValue (.literal 0)))
      else (thn, els)
  | _, _ => (thn, els)

mutual
/-- Local ids read by an op sequence (env lookups in operands / terminal
    returns). Used to decide which branch-bound locals the continuation
    actually consumes. -/
partial def localReadsOps : Array SrcOp → Array Nat
  | #[] => #[]
  | ops => ops.flatMap localReadsOp

partial def localReadsOp : SrcOp → Array Nat
  | .letLocal i v => localReadsVal v |>.filter (· != i)
  | .setLocal i v => localReadsVal v |>.filter (· != i)
  | .checkedAddU64 l r => localReadsVal l ++ localReadsVal r
  | .checkedSubU64 l r => localReadsVal l ++ localReadsVal r
  | .checkedMulU64 l r => localReadsVal l ++ localReadsVal r
  | .checkedDivU64 l r => localReadsVal l ++ localReadsVal r
  | .checkedModU64 l r => localReadsVal l ++ localReadsVal r
  | .ite _ l r thn els =>
      localReadsVal l ++ localReadsVal r ++
        (localReadsOps thn ++ localReadsOps els)
  | .forAccum _ v _ => localReadsVal v
  | .forBody _ body => localReadsOps body
  | .indexSet _ i v _ _ => localReadsVal i ++ localReadsVal v
  | .storeField _ v => localReadsVal v
  | .okState v => localReadsVal v
  | .returnU64 v => localReadsVal v
  | .returnState v => localReadsVal v
  | .externalCall _ args => args.flatMap localReadsVal
  | .emitEvent _ v => localReadsVal v
  | .indexSetLeaf _ i v _ _ => localReadsVal i ++ localReadsVal v
  | _ => #[]

partial def localReadsVal : SrcVal → Array Nat
  | .local i => #[i]
  | .field base _ => localReadsVal base
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r =>
      localReadsVal l ++ localReadsVal r
  | .bitNot v => localReadsVal v
  | .indexGet b _ i _ _ => localReadsVal b ++ localReadsVal i
  | .select _ l r t e =>
      localReadsVal l ++ localReadsVal r ++ localReadsVal t ++ localReadsVal e
  | .ext _ operands => operands.flatMap localReadsVal
  | _ => #[]

end



/-- Translate one op sequence (method body or one branch) to Plan statements.
    Returns the statements plus the post-sequence environment for branch merges. -/
partial def opsToStmts (ctx : Ctx) (leafNames : Array String)
    (ops : Array SrcOp) (st : SeqState) : Except String (Array Statement × SeqState) := do
  let mut out : Array Statement := #[]
  let mut cur := st
  let ops := if foldableErrorTail ops then ops.pop else ops
  for op in ops do
    -- A second consecutive value return folds into the aggregate; any other
    -- op after a return is rejected.
    if cur.returned && !(match op with | .returnU64 _ => true | _ => false) then
      return ← lowerError "statements after return"
    match op with
    | .letLocal i v =>
        let e ← valToExpr ctx cur.env v
        cur := { cur with env := cur.env.filter (·.1 != i) |>.push (i, e) }
    | .setLocal i v =>
        let e ← valToExpr ctx cur.env v
        cur := { cur with env := cur.env.filter (·.1 != i) |>.push (i, e) }
    | .joinLocal _ =>
        -- φ-join marker: the enclosing `ite` merge binds this local; unbound
        -- uses fail closed at the use site.
        pure ()
    | .checkedAddU64 l r =>
        cur := { cur with pending := some (.checkedAdd (← valToExpr ctx cur.env l)
          (← valToExpr ctx cur.env r)) }
    | .checkedSubU64 l r =>
        cur := { cur with pending := some (.checkedSub (← valToExpr ctx cur.env l)
          (← valToExpr ctx cur.env r)) }
    | .checkedMulU64 l r =>
        cur := { cur with pending := some (.checkedMul (← valToExpr ctx cur.env l)
          (← valToExpr ctx cur.env r)) }
    | .checkedDivU64 l r =>
        cur := { cur with pending := some (.checkedDiv (← valToExpr ctx cur.env l)
          (← valToExpr ctx cur.env r)) }
    | .checkedModU64 l r =>
        cur := { cur with pending := some (.checkedMod (← valToExpr ctx cur.env l)
          (← valToExpr ctx cur.env r)) }
    | .ite cmp l r thn els => do
        let condExpr : Expr := .compare cmp (← valToExpr ctx cur.env l)
          (← valToExpr ctx cur.env r)
        let (thnStmts, thnSt) ← opsToStmts ctx leafNames thn
          { cur with pending := none, sawStore := false }
        let (elsStmts, elsSt) ← opsToStmts ctx leafNames els
          { cur with pending := none, sawStore := false }
        -- φ-merge locals: a local whose value differs across arms becomes
        -- `select cond thn els`; the unchanged side falls back to the
        -- pre-branch binding. A local bound in exactly one arm and NOT read
        -- after the branch is branch-private (its binding dies with the
        -- arm); failing closed here would reject canonical
        -- `if c then (let x := …; store x) else revert` guard shapes.
        -- Branch-private bindings (a local bound in exactly one arm) are
        -- admissible when the opposing arm is a lone trap: the trap path
        -- never joins, so the binding dies with the arm (canonical
        -- `if c then (let x := …; …) else revert` guard shape). Otherwise
        -- require symmetric binding (unsound otherwise).
        let opposingTrap := isLoneTrap thnStmts || isLoneTrap elsStmts
        let keys :=
          (((thnSt.env.map (·.1)) ++ (elsSt.env.map (·.1))).toList.eraseDups).filter
            fun i =>
              if opposingTrap then
                -- a one-sided binding is fine; a two-sided one still merges
                (thnSt.env.find? (·.1 == i)).isSome &&
                  (elsSt.env.find? (·.1 == i)).isSome
              else true
        let mut merged := cur.env
        for i in keys do
          let before? := (cur.env.find? (·.1 == i)).map (·.2)
          let te? := (thnSt.env.find? (·.1 == i)).map (·.2)
          let ee? := (elsSt.env.find? (·.1 == i)).map (·.2)
          let te ←
            match te? with
            | some t => pure t
            | none =>
                match before? with
                | some old => pure old
                | none =>
                    if opposingTrap then pure (ee?.getD (.literal 0))
                    else lowerError s!"local {i} bound in the then branch only"
          let ee ←
            match ee? with
            | some e => pure e
            | none =>
                match before? with
                | some old => pure old
                | none =>
                    if opposingTrap then pure te
                    else lowerError s!"local {i} bound in the else branch only"
          unless te == ee do
            merged := merged.filter (·.1 != i) |>.push (i, Expr.select condExpr te ee)
        cur := { cur with env := merged }
        let (thnStmts, elsStmts) := balanceTrapArms thnStmts elsStmts
        unless thnStmts.isEmpty && elsStmts.isEmpty do
          out := out.push (.ifThenElse condExpr thnStmts elsStmts)
    | .forAccum n addend resultLocal => do
        -- Sum `addend` over [0, n): unroll n checked-add steps; the loop
        -- variable inside the addend becomes the literal step index k
        -- (PSY-LOOP semantics: bound assert at DPN lowering + per-step traps).
        unless n ≤ maxUnrollSteps do
          return ← lowerError s!"forAccum bound {n} exceeds the unroll limit {maxUnrollSteps}"
        let mut acc : Expr := .literal 0
        for k in [0:n] do
          let addendK ← valToExpr ctx cur.env (substituteLoopIxVal addend k)
          acc := .checkedAdd acc addendK
        cur := { cur with
          env := cur.env.filter (·.1 != resultLocal) |>.push (resultLocal, acc) }
    | .forBody n body => do
        -- State loop: unroll n guarded steps; loopIx inside the body becomes
        -- the literal step index. Body stores stay inside the step's branch
        -- statements (conditional under the step guard at DPN lowering).
        unless n ≤ maxUnrollSteps do
          return ← lowerError s!"forBody bound {n} exceeds the unroll limit {maxUnrollSteps}"
        for k in [0:n] do
          let (stmtsK, stK) ← opsToStmts ctx leafNames (substituteLoopIxOps body k) cur
          if stK.returned then
            return ← lowerError "return inside a loop body is not admitted"
          out := out.append stmtsK
          if stK.sawStore then
            cur := { stK with sawStore := true }
        pure ()
    | .indexSetLeaf name idx value _ leaf => do
        -- Unresolved vector leaf — the extractor resolves these against the schema
        -- before target lowering; seeing one here is an extractor bug.
        let _ ← valToExpr ctx cur.env idx
        let _ ← valToExpr ctx cur.env value
        return ← lowerError s!"unresolved vector leaf {name}.{leaf}"
    | .indexSet name idx value _ elemOff => do
        let some (baseLeaf, elementLeaves) := ctx.vectorOf name
          | return ← lowerError s!"unknown vector {name}"
        let some k := (match idx with | .lit n => some n.toNat | _ => none)
          | return ← lowerError s!"dynamic index into vector {name} (DPN state slots are static)"
        unless elemOff % 8 == 0 do
          return ← lowerError s!"vector {name} leaf byte offset {elemOff} is not limb-aligned"
        let ev ← valToExpr ctx cur.env value
        out := out.push (.store (baseLeaf + k * elementLeaves + elemOff / 8) ev)
        cur := { cur with sawStore := true }
    | .storeField name value => do
        let some idx := ctx.leafIndexOf name
          | return ← lowerError s!"unknown state leaf {name}"
        let ev ← valToExpr ctx cur.env value
        out := out.push (.store idx ev)
        cur := { cur with sawStore := true }
    | .okState v => do
        match cur.pending with
        | some checked =>
            if !cur.sawStore then
              -- Guard-folded shape only (no explicit store ran): store the
              -- checked result, return the post-store read (canonical
              -- `increment` shape).
              let dest := implicitDestLeaf ctx v
              out := out.push (.store dest checked)
              if ctx.retCount ≥ 1 then
                out := out.push (.returnValue (.stateLoad dest))
              else
                out := out.push .returnNone
            else if ctx.retCount ≥ 1 then
              -- Explicit storeField(s) already materialized every leaf;
              -- storing the pending expr again would double-write (and for
              -- cross-referencing stores, write the WRONG leaf).
              out := out.push (.returnValue (← valToExpr ctx cur.env v))
            else
              out := out.push .returnNone
        | none =>
            if !cur.sawStore then
              -- No explicit storeField: okState carries the state update
              -- implicitly (Core.Eval's implicit-destination convention).
              let dest := implicitDestLeaf ctx v
              let ev ← valToExpr ctx cur.env v
              out := out.push (.store dest ev)
            if ctx.retCount ≥ 1 then
              out := out.push (.returnValue (← valToExpr ctx cur.env v))
            else
              out := out.push .returnNone
        cur := { cur with pending := none, returned := true }
    | .errorOverflow =>
        out := out.push (.assertWithMessage (.boolLiteral false) "revert")
    | .errorNamed name =>
        -- PSY-TYPED-ERROR: zero-arg named revert tags the constructor name
        -- in the DPN assert record (structured payloads stay FC).
        out := out.push (.assertWithMessage (.boolLiteral false) s!"revert:{name}")
    | .errorTyped _ =>
        return ← lowerError "typed error payloads are not admitted in the psy-dpn-v1 slice"
    | .emitEvent name payload => do
        let e ← valToExpr ctx cur.env payload
        out := out.push (.emitEvent name #[e])
    | .externalCall callee args => do
        let argExprs ← args.mapM (valToExpr ctx cur.env)
        out := out.push (.externalCall callee argExprs)
    | .returnU64 v => do
        let e ← valToExpr ctx cur.env v
        let foldWith (prev : Statement) : Except String (Option Statement) :=
          match prev with
          | .returnValue p => pure (some (.returnAggregate #[p, e]))
          | .returnAggregate ps =>
              if ps.size ≥ 8 then
                .error "psy/lower: aggregate return exceeds 8 leaves"
              else pure (some (.returnAggregate (ps.push e)))
          | _ => pure none
        let folded : Option Statement ←
          match out.back? with
          | some prev => foldWith prev
          | none => pure none
        match folded with
        | some agg => out := out.pop; out := out.push agg
        | none => out := out.push (.returnValue e)
        cur := { cur with returned := true }
    | .returnState _ =>
        return ← lowerError "returnState outside init"
    | .ext payload => nomatch payload
  pure (out, cur)


/-- Lower one extracted method into a PlanFunction. -/
def lowerMethod (leafNames : Array String)
    (vectorOf : String → Option (Nat × Nat))
    (method : Extract.IR.Method) :
    Except String PlanFunction := do
  let isInit := method.kind == .init
  let ctx : Ctx := {
    leafIndexOf := fun name => leafNames.findIdx? (· == name)
    vectorOf
    paramCount := method.paramCount
    isInit
    retCount := method.retCount
  }
  let params : Array PlanParam := (Array.range method.paramCount).map fun i =>
    { sourceIndex := i
      name := s!"p{i}"
      isBool := method.paramTypes[i]? == some .boolean }
  if isInit then
    -- Canonical init: one `returnState v` per state leaf, declaration order.
    unless !method.ops.isEmpty do
      return ← lowerError s!"{method.ixName}: init has no returnState"
    let mut out : Array Statement := #[]
    let mut st : SeqState := {}
    for op in method.ops do
      match op with
      | .returnState v =>
          let idx := out.size
          if idx ≥ leafNames.size then
            return ← lowerError s!"{method.ixName}: init produces more leaves than the state schema"
          let e ← valToExpr ctx st.env v
          out := out.push (.store idx e)
      | .letLocal i v =>
          -- init computations: bind the local, keep building stores.
          let e ← valToExpr ctx st.env v
          st := { st with env := st.env.filter (·.1 != i) |>.push (i, e) }
      | _ =>
          return ← lowerError s!"{method.ixName}: non-returnState op in init"
    unless out.size == leafNames.size do
      return ← lowerError s!"{method.ixName}: init covers {out.size} of {leafNames.size} state leaves"
    out := out.push .returnNone
    return {
      index := 0
      name := method.ixName
      kind := .initialize
      params
      body := out
      resultIsBool := false
      resultIsUnit := true
    }
  else
    if method.ops.isEmpty then
      lowerError s!"{method.ixName}: empty ops"
    let (body, _) ← opsToStmts ctx leafNames method.ops {}
    return {
      index := 0
      name := method.ixName
      kind := .mutate
      params
      body
      resultIsBool := method.retTypes == #[.boolean]
      resultIsUnit := method.retCount == 0
    }

/-- Collect distinct `errorNamed` constructor names for the Plan error table. -/
private partial def collectErrorNames (ops : Array SrcOp) (acc : Array String) : Array String :=
  ops.foldl (init := acc) fun acc op =>
    match op with
    | .errorNamed name => if acc.contains name then acc else acc.push name
    | .ite _ _ _ thn els => collectErrorNames els (collectErrorNames thn acc)
    | .forBody _ body => collectErrorNames body acc
    | _ => acc

/-- Project and lower an extracted program into a Psy Plan. -/
def planFromExtracted (src : Extract.IR.Program) : Except String Plan := do
  for method in src.methods do
    unless method.annotations.isEmpty do
      return ← lowerError s!"psy cannot consume target annotations on {method.ixName}"
  let source ← Core.Target.projectProgram extractRegistration src
  if source.slots.isEmpty then
    lowerError "program has no slots"
  for slot in source.slots do
    unless slot.width == 1 || slot.width == 2 || slot.width == 4 || slot.width == 8 do
      lowerError s!"state leaf {slot.name} width {slot.width} is not Felt-carried (≤ 8 bytes)"
  let ctors := source.methods.filter (·.kind == .init)
  let errorNames := src.methods.foldl (init := #[])
      fun acc m => collectErrorNames m.ops acc
  let entries := source.methods.filter (·.kind != .init)
  if ctors.isEmpty then
    return ← lowerError "psy wants an init (constructor)"
  if entries.isEmpty then
    return ← lowerError "psy wants at least one entry method"
  let leafNames := source.slots.map (·.name)
  let vectorOf : String → Option (Nat × Nat) := fun name =>
    source.schema.vectors.find? (·.name == name) |>.bind fun vector =>
      (source.schema.vectorBaseLeafIndex? vector).map (·, vector.elementLeaves)
  let mut functions : Array PlanFunction := #[]
  for method in source.methods do
    let fn ← lowerMethod leafNames vectorOf
      { kind := method.kind
        name := method.name
        ixName := method.ixName
        paramCount := method.paramCount
        paramWidths := method.paramWidths
        paramTypes := method.paramTypes
        paramSchemas := method.paramSchemas
        retWidths := method.retWidths
        retTypes := method.retTypes
        retSchema := method.retSchema
        retCount := method.retCount
        annotations := method.annotations
        sketch := method.sketch
        ops := method.ops.map wrapOp }
    functions := functions.push { fn with index := functions.size }
  let plan : Plan := {
    programName := source.name
    stateFieldNames := leafNames
    functions
    errors := errorNames
  }
  Validate.validatePlan plan
  pure plan

end ProofForge.Psy.Lower
