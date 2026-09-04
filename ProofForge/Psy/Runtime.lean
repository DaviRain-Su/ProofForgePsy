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

/-!
## Statement effects (events / external calls)
-/

/-- `pf.emit` spelling: statement-level DPN event record. `name` is source
    metadata (the DPN record does not encode it); `x` is the payload word. -/
@[irreducible] def psyEvent (name : String) (x : UInt64) : UInt64 := x

/-- Void synchronous external call: hashed static qualified name. -/
@[irreducible] def psyVoidCall (callee : String) (args : Array UInt64) : UInt64 := 0

/-- Unit placeholder used by the extractor to instantiate a discard-bound
    effect continuation (`let _ := psyEvent …; rest`). -/
@[irreducible] def psyUnit : UInt64 := 0

/-- `pf.crypto.hashNoPad(args…)` (1..8 args): Poseidon over unpadded args,
    scalar product ABI = first HashOut limb. -/
@[irreducible] def hashNoPad (args : Array UInt64) : UInt64 :=
  args.foldl (init := 0) fun acc a => acc ^^^ a

/-- `pf.crypto.hashPad(args…)` (1..8 args): Poseidon over zero-padded args,
    first HashOut limb. -/
@[irreducible] def hashPad (args : Array UInt64) : UInt64 :=
  hashNoPad args

/-- `pf.crypto.hashTwoToOne(l0..l3, r0..r3)` (exactly 8 args): Poseidon over
    two 4-limb HashOuts, first limb. -/
@[irreducible] def hashTwoToOne (args : Array UInt64) : UInt64 :=
  hashNoPad args

/-- `pf.crypto.keccak256(words…)` (1..16 args): keccak over UInt64 words,
    first u32 limb as UInt64. -/
@[irreducible] def keccak256 (args : Array UInt64) : UInt64 :=
  args.foldl (init := 0) fun acc a => acc * 31 + a

/-- Full HashOut product ABI: `pf.crypto.hashNoPadFull(args, limb)` — one
limb (0..3) of the HashOut. Official simulate fills hash_out_arrays for
hashNoPad/hashTwoToOne; Array4 return aggregates over 4 limb calls (HashOut
CSE dedups to one circuit op). -/
@[irreducible] def hashNoPadFull (args : Array UInt64) (limb : UInt64) : UInt64 :=
  hashNoPad args

/-- Full HashOut product ABI: hashTwoToOne limb (0..3). -/
@[irreducible] def hashTwoToOneFull (args : Array UInt64) (limb : UInt64) : UInt64 :=
  hashTwoToOne args

/-- `pf.imt.get(key)`: self-contract current IMT value at `key`. -/
@[irreducible] def imtGet (_key : UInt64) : UInt64 := _key

/-- `pf.imt.contains(key)`: 0/1 membership flag. -/
@[irreducible] def imtContains (_key : UInt64) : UInt64 := 1

/-- `pf.imt.set(key, value)`: writes and returns the value. -/
@[irreducible] def imtSet (_key value : UInt64) : UInt64 := value

/-- `pf.imt.getExternal(contractId, key)`: same-user other-contract read. -/
@[irreducible] def imtGetExternal (_contractId key : UInt64) : UInt64 := key

/-- `pf.imt.getOther(userId, contractId, key)`: cross-user read. -/
@[irreducible] def imtGetOther (_userId _contractId key : UInt64) : UInt64 := key

/-- `pf.imt.containsOther(userId, contractId, key)`: cross-user membership. -/
@[irreducible] def imtContainsOther (_userId _contractId _key : UInt64) : UInt64 := 1

end ProofForge.Psy.Runtime
