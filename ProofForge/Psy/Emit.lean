/-
  Psy Emit: validated Psy Plan → canonical DPN package JSON.

  Pipeline: `Psy.Lower.planFromExtracted` → `Psy.Dpn.Lower.lowerPlanToPackageV1`
  → `Psy.Dpn.JsonCodec.encodePackageCompact`. This module is the thin
  product surface the commands and registry consume, plus the Plan-level
  canonical digest used as the registry pin.
-/
import ProofForge.Psy.Lower
import ProofForge.Psy.Dpn.Lower
import ProofForge.Psy.Dpn.JsonCodec

namespace ProofForge.Psy.Emit

open ProofForge.Psy

/-- Package for a Plan directly (tests / tools). -/
def packageOfPlan (plan : Plan.Plan) : Except String Dpn.Schema.PackageV1 :=
  Dpn.Lower.lowerPlanToPackageV1 plan

/-- Lower an extracted program to a validated Plan. -/
def planOfExtracted (src : Extract.IR.Program) : Except String Plan.Plan :=
  Lower.planFromExtracted src

/-- Lower an extracted program to the canonical DPN package. -/
def emitPackage (src : Extract.IR.Program) :
    Except String Dpn.Schema.PackageV1 :=
  Lower.planFromExtracted src >>= packageOfPlan

/-- Compact canonical package JSON for an extracted program. -/
def emitPackageJson (src : Extract.IR.Program) : Except String String := do
  let pkg ← emitPackage src
  pure (Dpn.JsonCodec.encodePackageCompact pkg)

/-- Compact canonical package JSON from a lowered Plan. -/
def emitPackageJsonOfPlan (plan : Plan.Plan) : Except String String := do
  let pkg ← packageOfPlan plan
  pure (Dpn.JsonCodec.encodePackageCompact pkg)

/-- Canonical Plan digest: FNV-1a 64 over the stable Plan rendering.
    Pins the registry against accidental extractor drift. -/
def planDigestHex (plan : Plan.Plan) : String :=
  Core.IR.u64Hex (Core.IR.fnv1a64 (Plan.renderCanonical plan))

end ProofForge.Psy.Emit