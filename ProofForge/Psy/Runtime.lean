namespace ProofForge.Psy.Runtime

/-!
Psy DPN execution-context leaves.

These are the contract-facing spellings of the DPN `ExecutionContext` reads
(`DPNOpType` 46–50, 79, 80 in the pinned psy-node schema). They are
irreducible host reads: the extractor recognizes each constant by name and
emits the matching `Psy.Ops.ValKind` leaf. On the Lean side they elaborate as
`0`, so kernel proofs and unit tests over `@[pf_entry]` definitions never
depend on a concrete chain context.

All values are Felt-carried `UInt64` scalars. `GetUserPublicKeyHash` (50) and
`GetSessionProofTreeRoot` (80) are HashOut-typed upstream; the product ABI
exposes the first limb only (official simulate injects zero-filled limbs).
-/

/-- DPN `GetUserId` (op 46): the current user id. -/
@[irreducible] def psyUserId : UInt64 := 0

/-- DPN `GetContractId` (op 47): the current contract id. -/
@[irreducible] def psyContractId : UInt64 := 0

/-- DPN `GetCheckpointId` (op 48): the current checkpoint id. -/
@[irreducible] def psyCheckpointId : UInt64 := 0

/-- DPN `GetNonce` (op 49): the current transaction nonce. -/
@[irreducible] def psyNonce : UInt64 := 0

/-- DPN `GetCallerContractId` (op 79): the calling contract id
(`0` on a user-originated call under official simulate). -/
@[irreducible] def psyCallerContractId : UInt64 := 0

/-- DPN `GetUserPublicKeyHash` (op 50), first HashOut limb.
Official simulate defaults the hash to `[0; 4]`, so the product value is `0`
unless the host injects one. -/
@[irreducible] def psyUserPublicKeyHash : UInt64 := 0

/-- DPN `GetSessionProofTreeRoot` (op 80), first HashOut limb.
Official simulate injects no session root, so the product value is `0`. -/
@[irreducible] def psySessionProofTreeRoot : UInt64 := 0

end ProofForge.Psy.Runtime
