import Lake
open Lake DSL

package «proofforge-psy» where
  version := v!"0.0.1"

/-- Shared Attr + Core/Crypto surface used by the Psy SDK. -/
lean_lib ProofForgeCore where
  roots := #[
    `ProofForge.Attr,
    `ProofForge.Core.Codec,
    `ProofForge.Core.Collections,
    `ProofForge.Core.Math,
    `ProofForge.Core.Ops,
    `ProofForge.Core.SafeCast,
    `ProofForge.Core.Value
  ]

/-- Contract-facing Psy SDK: the DPN execution-context leaves the extractor
    recognizes by name. No compiler machinery. -/
lean_lib ProofForgePsySdk where
  roots := #[
    `ProofForge.Psy.Runtime
  ]

/-- Compiler: Extract, Psy Plan/IR/DPN Emit/Registry, and the `ProofForge` umbrella. -/
@[default_target]
lean_lib ProofForge where
  roots := #[
    `ProofForge,
    `ProofForge.Cli,
    `ProofForge.Core.CFG,
    `ProofForge.Core.Eval,
    `ProofForge.Core.FixedPoint,
    `ProofForge.Core.IR,
    `ProofForge.Core.Schema,
    `ProofForge.Core.Target,
    `ProofForge.Crypto.Keccak,
    `ProofForge.Crypto.Sha256,
    `ProofForge.Psy.Ops,
    `ProofForge.Psy.Plan,
    `ProofForge.Psy.Validate,
    `ProofForge.Psy.Lower,
    `ProofForge.Psy.Dpn.Schema,
    `ProofForge.Psy.Dpn.JsonCodec,
    `ProofForge.Psy.Dpn.Lower,
    `ProofForge.Psy.Emit,
    `ProofForge.Psy.Registry,
    `ProofForge.Psy.Commands,
    `ProofForge.Extract,
    `ProofForge.Extract.IR,
    `ProofForge.Extract.Ops,
    `ProofForge.Extract.Lexical,
    `ProofForge.Extract.Decode,
    `ProofForge.Profile
  ]

/-- Build every module under `Examples/` (Psy fixtures only). -/
lean_lib Examples where
  globs := #[.one `Examples, .submodules `Examples]

lean_lib Tests

lean_exe psyGolden where
  root := `Tests.PsyGolden
  supportInterpreter := true

lean_exe pf where
  root := `ProofForge.Cli
  supportInterpreter := true
