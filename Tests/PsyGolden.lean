/-
  Psy DPN golden tests: the Counter three-method package emitted through the
  full fork pipeline (extract → Plan → DPN lower) must be structurally equal
  to the V2 hand-built golden `counterPackageGoldenV1`, and the pinned
  method ids must match the official SHA-256 algorithm.
-/
import ProofForge.Extract
import ProofForge.Psy.Emit
import ProofForge.Psy.Dpn.Lower
import ProofForge.Psy.Dpn.JsonCodec

namespace Tests.PsyGolden

open ProofForge
open ProofForge.Psy

private def expect (cond : Bool) (message : String) : IO Unit := do
  if cond then pure () else throw <| IO.userError s!"psy golden: {message}"

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

/-- Extract the in-tree Counter fixture through the product pipeline. -/
unsafe def extractedCounterPlan : IO (Except String Plan.Plan) := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Examples.Psy.Counter }] {} (loadExts := true)
  return Extract.extractModuleIR env `Examples.Psy.Counter none >>= Emit.planOfExtracted

/-- The extracted Counter package must equal the hand-built golden
    for the three canonical methods. -/
unsafe def testCounterExtractedMatchesGolden : IO Unit := do
  match ← extractedCounterPlan with
  | .error reason => throw <| IO.userError s!"extract failed: {reason}"
  | .ok plan =>
      let pkg ←
        match Emit.packageOfPlan plan with
        | .error reason => throw <| IO.userError s!"lower failed: {reason}"
        | .ok pkg => pure pkg
      let golden := counterPackageGoldenV1
      for g in golden do
        match pkg.find? (·.name == g.name) with
        | none => throw <| IO.userError s!"missing method {g.name}"
        | some m =>
            if m != g then
              throw <| IO.userError s!"method {g.name} differs from golden:\n  mine:   {repr m}\n  golden: {repr g}"
      -- method ids from the official algorithm
      for fn in pkg do
        let expected :=
          match fn.name with
          | "get" => Dpn.Lower.genDapenContractFunctionMethodIdV1 "get" #[]
          | "increment" => Dpn.Lower.genDapenContractFunctionMethodIdV1 "increment" #[("p0", 1)]
          | "initialize" => Dpn.Lower.genDapenContractFunctionMethodIdV1 "initialize" #[("p0", 1)]
          | _ => fn.methodId
        if fn.methodId != expected then
          throw <| IO.userError s!"method_id mismatch for {fn.name}: {fn.methodId} != {expected}"

/-- Canonical JSON round-trip: encode → parse → structural equality. -/
def testEncodeRoundTrip : IO Unit := do
  let encoded := Dpn.JsonCodec.encodePackageCompact counterPackageGoldenV1
  match Dpn.JsonCodec.parsePackage? encoded with
  | none => throw <| IO.userError s!"failed to parse our encode: {encoded}"
  | some pkg =>
      if pkg != counterPackageGoldenV1 then
        throw <| IO.userError "encodePackageCompact round-trip must preserve Counter package"

unsafe def main : IO UInt32 := do
  testEncodeRoundTrip
  testCounterExtractedMatchesGolden
  IO.println "psy golden: all checks passed"
  return 0

end Tests.PsyGolden

unsafe def main : IO UInt32 := Tests.PsyGolden.main
