import ProofForge.Extract.IR
import ProofForge.Core.Ops

namespace ProofForge.Extract.Ops

/-- Decoder-facing names over the extensible extraction dialect; no second Ops tree is created. -/
abbrev Cmp := IR.Cmp
abbrev Val := IR.Val
abbrev Op := IR.Op

private def psyLeaf (kind : Psy.Ops.ValKind) : Val :=
  .ext (.psy kind) #[]

@[match_pattern] def Val.psyUserId : Val := psyLeaf .ctxUserId
@[match_pattern] def Val.psyContractId : Val := psyLeaf .ctxContractId
@[match_pattern] def Val.psyCheckpointId : Val := psyLeaf .ctxCheckpointId
@[match_pattern] def Val.psyNonce : Val := psyLeaf .ctxNonce
@[match_pattern] def Val.psyCallerContractId : Val := psyLeaf .ctxCallerContractId
@[match_pattern] def Val.psyUserPublicKeyHash : Val := psyLeaf .ctxUserPublicKeyHash
@[match_pattern] def Val.psySessionProofTreeRoot : Val := psyLeaf .ctxSessionProofTreeRoot

private partial def walk (ops : Array Op) (predicate : Op → Bool) : Bool :=
  ops.any fun op =>
    predicate op ||
      match op with
      | .ite _ _ _ thn els => walk thn predicate || walk els predicate
      | .forBody _ body => walk body predicate
      | _ => false

def hasCheckedArith (ops : Array Op) : Bool :=
  walk ops fun
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. => true
    | _ => false

def hasForAccum (ops : Array Op) : Bool :=
  walk ops fun | .forAccum .. => true | _ => false

def hasIndexSet (ops : Array Op) : Bool :=
  walk ops fun | .indexSetLeaf .. | .indexSet .. => true | _ => false

def hasStoreField (ops : Array Op) : Bool :=
  walk ops fun | .storeField .. => true | _ => false

partial def isLangLeaf : Val → Bool
  | .local _ | .loopIx | .select .. | .bitAnd .. | .bitOr .. | .bitXor ..
  | .bitNot .. | .shiftL .. | .shiftR .. | .indexGet .. => true
  | .field base _ => isLangLeaf base
  | .ext _ operands => operands.any isLangLeaf
  | _ => false

private partial def hasSelectVal : Val → Bool
  | .select .. => true
  | .field base _ | .bitNot base => hasSelectVal base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      hasSelectVal lhs || hasSelectVal rhs
  | .indexGet base _ index _ _ => hasSelectVal base || hasSelectVal index
  | .ext _ operands => operands.any hasSelectVal
  | _ => false

private partial def isBitVal : Val → Bool
  | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR .. => true
  | .field base _ => isBitVal base
  | .select _ lhs rhs thn els =>
      isBitVal lhs || isBitVal rhs || isBitVal thn || isBitVal els
  | .ext _ operands => operands.any isBitVal
  | _ => false

private def opValuesAny (predicate : Val → Bool) : Op → Bool
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      predicate value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
  | .indexSetLeaf _ lhs rhs _ _ | .indexSet _ lhs rhs _ _ => predicate lhs || predicate rhs
  | .ext payload => nomatch payload
  | .errorTyped frame => frame.values.any predicate
  | .joinLocal _ | .forBody _ _ | .errorOverflow | .errorNamed _ => false

private partial def isPsyContext : Val → Bool
  | .ext (.psy _) _ => true
  | .field base _ | .bitNot base => isPsyContext base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      isPsyContext lhs || isPsyContext rhs
  | .indexGet base _ index _ _ => isPsyContext base || isPsyContext index
  | .select _ lhs rhs thn els =>
      isPsyContext lhs || isPsyContext rhs || isPsyContext thn || isPsyContext els
  | _ => false

def hasPsyLeaf (ops : Array Op) : Bool :=
  walk ops (opValuesAny isPsyContext)

def hasLangOp (ops : Array Op) : Bool :=
  walk ops fun op =>
    match op with
    | .forAccum .. | .forBody .. | .indexSetLeaf .. | .indexSet .. | .errorNamed _ => true
    | _ => opValuesAny (fun value => isLangLeaf value || isBitVal value || hasSelectVal value) op

/-- Psy mutating methods admit context reads and any structured-state op as evidence;
    there is no target effect vocabulary in v1. -/
def hasPsyEffect (ops : Array Op) : Bool :=
  hasPsyLeaf ops

end ProofForge.Extract.Ops
