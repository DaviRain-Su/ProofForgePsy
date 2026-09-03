/-
  Psy DPN golden tests: the Counter three-method package emitted through the
  full fork pipeline (extract → Plan → DPN lower) must be structurally equal
  to the V2 hand-built golden `counterPackageGoldenV1`, and the pinned
  method ids must match the official SHA-256 algorithm.

  The extraction runs at ELABORATION time (`#pf_psy_golden_guard` reads the
  compile-time environment of the imported Counter fixture) instead of a
  runtime `importModules` executable. Compile-time checks avoid the
  cross-package module-resolution fragility of runtime import executables
  (each package owns files under the shared `ProofForge/` root directory,
  which Lean's directory-short-circuit lookup shadows).
-/
import ProofForge.Extract
import ProofForge.Psy.Emit
import ProofForge.Psy.Dpn.Lower
import ProofForge.Psy.Commands
import Examples.Psy.Counter

namespace Tests.PsyGolden

open ProofForge
open ProofForge.Psy

/-- The hand-built Counter golden, byte-equal to V2's `counterPackageGoldenV1`. -/
def counterPackageGoldenV1 : Dpn.Schema.PackageV1 :=
  #[ Dpn.Lower.lowerFunctionForTestV1
      { index := 0, name := "get", kind := .mutate
        params := #[], body := #[.returnValue (.stateLoad 0)]
        resultIsBool := false, resultIsUnit := false } false
  |>.toOption.get!
  , Dpn.Lower.lowerFunctionForTestV1
      { index := 1, name := "increment", kind := .mutate
        params := #[{ sourceIndex := 0, name := "p0", isBool := false }]
        body := #[.store 0 (.checkedAdd (.stateLoad 0) (.param 0)),
                  .returnValue (.stateLoad 0)]
        resultIsBool := false, resultIsUnit := false } false
  |>.toOption.get!
  , Dpn.Lower.lowerFunctionForTestV1
      { index := 2, name := "initialize", kind := .initialize
        params := #[{ sourceIndex := 0, name := "p0", isBool := false }]
        body := #[.store 0 (.param 0), .returnNone]
        resultIsBool := false, resultIsUnit := true } false
  |>.toOption.get! ]

open Lean Elab Command

/-- Canonical JSON round-trip: encode → parse → structural equality. -/
def testEncodeRoundTrip : Except String Unit := do
  let encoded := Dpn.JsonCodec.encodePackageCompact counterPackageGoldenV1
  match Dpn.JsonCodec.parsePackage? encoded with
  | none => throw s!"failed to parse our encode: {encoded}"
  | some pkg =>
      if pkg != counterPackageGoldenV1 then
        throw "encodePackageCompact round-trip must preserve Counter package"

/-- Full-pipeline check: extract the imported Counter fixture, lower it, and
    compare against the hand-built golden including pinned method ids. Runs
    during elaboration of this module (compile-time environment). -/
elab "#pf_psy_golden_guard" : command => do
  let ns := `Examples.Psy.Counter
  let src ←
    match ← liftCoreM do
      let env ← getEnv
      pure (Extract.extractModuleIR env ns none) with
    | .error reason => throwError reason
    | .ok src => pure src
  let plan ←
    match Emit.planOfExtracted src with
    | .error reason => throwError reason
    | .ok plan => pure plan
  let pkg ←
    match Emit.packageOfPlan plan with
    | .error reason => throwError reason
    | .ok pkg => pure pkg
  let golden := Tests.PsyGolden.counterPackageGoldenV1
  for g in golden do
    match pkg.find? (·.name == g.name) with
    | none => throwError s!"psy golden: missing method {g.name}"
    | some m =>
        if m != g then
          throwError s!"psy golden: method {g.name} differs from golden"
  -- method ids from the official algorithm
  for fn in pkg do
    let expected :=
      match fn.name with
      | "get" => Dpn.Lower.genDapenContractFunctionMethodIdV1 "get" #[]
      | "increment" => Dpn.Lower.genDapenContractFunctionMethodIdV1 "increment" #[("p0", 1)]
      | "initialize" => Dpn.Lower.genDapenContractFunctionMethodIdV1 "initialize" #[("p0", 1)]
      | _ => fn.methodId
    if fn.methodId != expected then
      throwError s!"psy golden: method_id mismatch for {fn.name}: {fn.methodId} != {expected}"
  match Tests.PsyGolden.testEncodeRoundTrip with
  | .ok _ => pure ()
  | .error reason => throwError reason

#pf_psy_golden_guard

end Tests.PsyGolden