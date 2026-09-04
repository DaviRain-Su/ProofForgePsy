/-
  G5-WIDE end-to-end test: hand-built PlanFunctions using the wide bind
  statements lower through the DPN builder to concrete circuits. Each case
  asserts the lowering succeeds (no FC) and the resulting definitions contain
  the expected G5-WIDE ops.
-/
import Lean
import ProofForge.Psy.Plan
import ProofForge.Psy.Dpn.Lower

namespace Tests.PsyWide

open ProofForge.Psy.Plan
open ProofForge.Psy.Dpn.Lower

def limb (i : Nat) : Expr := .literal (UInt64.ofNat i)

/-- UInt128 multiply: limbs [0,1] x [2,3] → 2-limb result. -/
def wideMulFn : PlanFunction :=
  { index := 0, name := "wideMul", kind := .mutate
    params := #[], resultIsBool := false, resultIsUnit := false
    body := #[
      .bindWideUintMul 128 0 (#[limb 1, limb 2, limb 3, limb 4]) (#[limb 5, limb 6, limb 7, limb 8]),
      .returnValue (.wideUintMulLimb 128 0 0)
    ] }

/-- UInt128 divmod quotient limb. -/
def wideDivFn : PlanFunction :=
  { index := 0, name := "wideDiv", kind := .mutate
    params := #[], resultIsBool := false, resultIsUnit := false
    body := #[
      .bindWideUintDivMod .quotient 128 1 (#[limb 100, limb 200, limb 300, limb 400]) (#[limb 3, limb 4, limb 5, limb 6]),
      .returnValue (.wideUintDivModLimb .quotient 128 1 0)
    ] }

/-- UInt128 shift-left limb. -/
def wideShlFn : PlanFunction :=
  { index := 0, name := "wideShl", kind := .mutate
    params := #[], resultIsBool := false, resultIsUnit := false
    body := #[
      .bindWideUintShift .shl 128 2 (#[limb 1, limb 2, limb 3, limb 4]) (.literal 3),
      .returnValue (.wideUintShiftLimb .shl 128 2 0)
    ] }

/-- UInt128 shift-right limb. -/
def wideShrFn : PlanFunction :=
  { index := 0, name := "wideShr", kind := .mutate
    params := #[], resultIsBool := false, resultIsUnit := false
    body := #[
      .bindWideUintShift .shr 128 3 (#[limb 1, limb 2, limb 3, limb 4]) (.literal 3),
      .returnValue (.wideUintShiftLimb .shr 128 3 1)
    ] }

open Lean Elab Command

/-- Assert the G5-WIDE lowerer emits an `add`-heavy circuit for wideMul. -/
def testWideMul : Except String Unit := do
  let some circ := lowerFunctionForTestV1 wideMulFn false |>.toOption | throw "wideMul failed"
  unless circ.definitions.any (·.opType == .add) do
    throw "wideMul should emit add ops (schoolbook product)"
  unless circ.definitions.size > 4 do
    throw s!"wideMul definitions too small: {circ.definitions.size}"

/-- Assert wideDiv emits a div-related circuit with assertions. -/
def testWideDiv : Except String Unit := do
  let some circ := lowerFunctionForTestV1 wideDivFn false |>.toOption | throw "wideDiv failed"
  unless circ.assertions.any (fun a => a.message.contains "div by zero") do
    throw "wideDiv should assert div-by-zero"
  unless circ.definitions.any (·.opType == .sub) do
    throw "wideDiv should emit sub ops (restoring subtract)"

/-- Assert wideShl emits u32 shift-left ops. -/
def testWideShl : Except String Unit := do
  let some circ := lowerFunctionForTestV1 wideShlFn false |>.toOption | throw "wideShl failed"
  unless circ.definitions.any (·.opType == .u32ShiftLeft) do
    throw "wideShl should emit u32 shift-left"

/-- Assert wideShr emits u32 shift-right ops. -/
def testWideShr : Except String Unit := do
  let some circ := lowerFunctionForTestV1 wideShrFn false |>.toOption | throw "wideShr failed"
  unless circ.definitions.any (·.opType == .u32ShiftRight) do
    throw "wideShr should emit u32 shift-right"

elab "#pf_psy_wide_guard" : command => do
  let results := #[testWideMul, testWideDiv, testWideShl, testWideShr]
  for r in results do
    match r with
    | .ok () => pure ()
    | .error e =>
        throwError s!"G5-WIDE guard failed: {e}"


#pf_psy_wide_guard

end Tests.PsyWide