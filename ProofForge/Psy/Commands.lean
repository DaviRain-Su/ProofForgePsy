/-
  Psy `#pf_*` commands: check / dump extracted ops / build DPN package.

  Mirrors `ProofForge.Evm.Commands` on the Psy pipeline:
  `Extract.extractModuleIR → Psy.Lower.planFromExtracted →
   Psy.Dpn.Lower.lowerPlanToPackageV1 → JsonCodec.encodePackageCompact`.
-/
import Lean
import ProofForge.Extract
import ProofForge.Profile
import ProofForge.Psy.Emit
import ProofForge.Psy.Registry

open Lean Elab Command
open ProofForge
open ProofForge.Psy

namespace ProofForge.Psy.Commands

/-- Chain-neutral profile gate: accept/reject a declaration per `ProofForge.Profile`. -/
elab "#pf_check " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let env ← getEnv
  match Profile.check env name with
  | .accept => logInfo m!"proofforge: accept {name}"
  | .reject reason => throwError reason

/-- Chain-neutral constant dumper. -/
elab "#pf_dump " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let env ← getEnv
  match env.find? name with
  | none => throwError "unknown {name}"
  | some info =>
    match info.value? with
    | none => throwError "no value {name}"
    | some e => logInfo m!"{name} := {e}"

private def extractPlan (ns : Name) : CoreM <| Except String Plan.Plan := do
  let env ← getEnv
  return Extract.extractModuleIR env ns none >>= Emit.planOfExtracted

/-- Extract the raw extensible program (pre-Plan) for diagnostics. -/
private def extractRawProgram (ns : Name) :
    CoreM <| Except String Extract.IR.Program := do
  let env ← getEnv
  return Extract.extractModuleIR env ns none

/-- Extract + lower a module namespace to a Psy Plan and print its shape. -/
elab "#pf_psy_build " n:ident : command => do
  let ns := n.getId
  match ← liftCoreM (extractPlan ns) with
  | .error reason => throwError reason
  | .ok plan => do
      let digest := Emit.planDigestHex plan
      match Registry.digestOf plan.programName with
      | some want =>
          if digest != want then
            throwError s!"ir/mismatch: extracted psy {plan.programName} digest {digest} != fixture {want}"
      | none => pure ()
      logInfo m!"proofforge-psy: program {plan.programName} slots = {plan.stateFieldNames}"
      logInfo m!"proofforge-psy: entries = {plan.functions.map (·.name)}"
      logInfo m!"proofforge-psy: digest = {digest}"
      match Emit.packageOfPlan plan with
      | .error reason => throwError reason
      | .ok pkg =>
          let json := Dpn.JsonCodec.encodePackageCompact pkg
          logInfo m!"proofforge-psy: emitted {json.length} bytes of DPN package JSON"

/-- Extract + dump the Psy Plan for a module namespace. -/
elab "#pf_psy_dump " n:ident : command => do
  let ns := n.getId
  match ← liftCoreM (extractRawProgram ns) with
  | .error reason => throwError reason
  | .ok raw =>
      for method in raw.methods do
        logInfo m!"proofforge-psy-dump: {method.ixName} retCount={method.retCount} \
          ops={method.ops.size}"
  match ← liftCoreM (extractPlan ns) with
  | .error reason => throwError reason
  | .ok plan => do
      logInfo m!"proofforge-psy-dump: {plan.programName} fields = {plan.stateFieldNames}"
      for fn in plan.functions do
        logInfo m!"proofforge-psy-dump: {fn.name} params={fn.params.size} \
          kind={repr fn.kind} body={repr fn.body}"
      -- Ret-arity surface: multi-value returns are fail-closed at Plan
      -- lowering; the dump shows the extractor's retCount for diagnosis.

      logInfo m!"proofforge-psy-dump: digest = {Emit.planDigestHex plan}"

end ProofForge.Psy.Commands