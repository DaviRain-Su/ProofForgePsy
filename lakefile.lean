import Lake
open Lake DSL

package «proofforge-psy» where
  version := v!"0.0.1"

/-- Shared Attr + Core/Crypto surface, maintained in ProofForgeCommon.
    Tracks ProofForgeCommon main; Common CI gates every push, so a
    -- breakage surfaces in these repositories' CI immediately. -/
require «proofforge-common» from git
  "https://github.com/DaviRain-Su/ProofForgeCommon.git" @ "main"

/-- Contract-facing Psy SDK: the DPN execution-context leaves the extractor
    recognizes by name. No compiler machinery. -/
lean_lib ProofForgePsySdk where
  roots := #[
    `ProofForge.Psy.Runtime
  ]

/-- Compiler: Extract, Psy Plan/IR/DPN Emit/Registry, and the `ProofForge` umbrella.
    The lib is named `ProofForgePsy` (not `ProofForge`): a lean_lib name claims its
    namespace for this package and would shadow the `ProofForge.Core.*` /
    `ProofForge.Crypto.*` modules exported by `proofforge-common`. -/
@[default_target]
lean_lib ProofForgePsy where
  globs := #[
    .one `ProofForge,
    .one `ProofForge.Cli,
    .submodules `ProofForge.Psy,
    .one `ProofForge.Extract,
    .submodules `ProofForge.Extract
  ]

/-- Build every module under `Examples/` (Psy fixtures only). -/
lean_lib Examples where
  globs := #[.one `Examples, .submodules `Examples]

lean_lib Tests where
  globs := #[.submodules `Tests]

lean_exe psyGolden where
  root := `Tests.PsyGolden
  supportInterpreter := true

lean_exe pf where
  root := `ProofForge.Cli
  supportInterpreter := true
