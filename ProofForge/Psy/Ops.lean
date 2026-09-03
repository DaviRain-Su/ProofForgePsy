import ProofForge.Core.Ops

namespace ProofForge.Psy.Ops

/-- Psy-only source value intrinsics. Recursive operands live in `Core.Ops.Val.ext`.

    v1 admits exactly the DPN `ExecutionContext` reads (psy-node pinned
    `DPNOpType` 46–50, 79, 80). Every leaf is nullary; hashing and IMT state
    effects are not admitted by this extractor slice and fail closed. -/
inductive ValKind where
  | ctxUserId
  | ctxContractId
  | ctxCheckpointId
  | ctxNonce
  | ctxCallerContractId
  | ctxUserPublicKeyHash
  | ctxSessionProofTreeRoot
  deriving BEq, Repr, Inhabited, DecidableEq

def ValKind.arity : ValKind → Nat :=
  fun _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- Psy v1 owns no effect extensions: the source slice (scalar state, Except
    errors, control flow, fixed vectors, context reads) never produces
    `Op.ext`. The type is intentionally empty so any future extension is an
    explicit, reviewable constructor. -/
inductive OpExt (V : Type) where
  deriving BEq, Repr

/-- No payloads exist; elimination is by `nomatch`. -/
def OpExt.elim {V : Type} {motive : OpExt V → Sort _} (x : OpExt V) : motive x :=
  nomatch x

def OpExt.wellFormed (x : OpExt Val) : Bool :=
  nomatch x

def Op.wellFormed (op : ProofForge.Core.Ops.Op ValKind OpExt) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Psy.Ops
