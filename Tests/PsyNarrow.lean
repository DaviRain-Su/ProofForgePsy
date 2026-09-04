/-
  R-HARD narrow UInt{8,16,32} end-to-end test: hand-built PlanFunctions using
  the narrow Expr constructors lower through the DPN builder. Each case asserts
  the lowering succeeds and the resulting circuit contains the expected
  narrow width guard (overflow / underflow / div-by-zero assert).
-/
import Lean
import ProofForge.Psy.Plan
import ProofForge.Psy.Dpn.Lower

namespace Tests.PsyNarrow

open ProofForge.Psy.Plan
open ProofForge.Psy.Dpn.Lower

def lit (i : Nat) : Expr := .literal (UInt64.ofNat i)

/-- UInt8 checked add: assert `sum < 256`. -/
def narrowAddFn : PlanFunction :=
  { index := 0, name := "narrowAdd", kind := .mutate
    params := #[], resultIsBool := false, resultIsUnit := false
    body := #[
      .returnValue (.narrowCheckedAdd 8 (lit 10) (lit 20))
    ] }

/-- UInt16 checked sub: assert `l >= r`. -/
def narrowSubFn : PlanFunction :=
  { index := 0, name := "narrowSub", kind := .mutate
    params := #[], resultIsBool := false, resultIsUnit := false
    body := #[
      .returnValue (.narrowCheckedSub 16 (lit 100) (lit 20))
    ] }

/-- UInt32 checked div: assert `r > 0`. -/
def narrowDivFn : PlanFunction :=
  { index := 0, name := "narrowDiv", kind := .mutate
    params := #[], resultIsBool := false, resultIsUnit := false
    body := #[
      .returnValue (.narrowCheckedDiv 32 (lit 100) (lit 4))
    ] }

/-- UInt8 checked shl: count < 8 + result < 256. -/
def narrowShlFn : PlanFunction :=
  { index := 0, name := "narrowShl", kind := .mutate
    params := #[], resultIsBool := false, resultIsUnit := false
    body := #[
      .returnValue (.narrowShl 8 (lit 1) (lit 3))
    ] }

open Lean Elab Command

/-- UInt8 add: assert "u8 add overflow". -/
def testNarrowAdd : Except String Unit := do
  let some circ := lowerFunctionForTestV1 narrowAddFn false |>.toOption | throw "narrowAdd failed"
  unless circ.assertions.any (fun a => a.message == "u8 add overflow") do
    throw "narrowAdd should assert u8 add overflow"

/-- UInt16 sub: assert "u16 sub underflow". -/
def testNarrowSub : Except String Unit := do
  let some circ := lowerFunctionForTestV1 narrowSubFn false |>.toOption | throw "narrowSub failed"
  unless circ.assertions.any (fun a => a.message == "u16 sub underflow") do
    throw "narrowSub should assert u16 sub underflow"

/-- UInt32 div: assert "u32 div by zero". -/
def testNarrowDiv : Except String Unit := do
  let some circ := lowerFunctionForTestV1 narrowDivFn false |>.toOption | throw "narrowDiv failed"
  unless circ.assertions.any (fun a => a.message == "u32 div by zero") do
    throw "narrowDiv should assert u32 div by zero"

/-- UInt8 shl: count guard + width guard. -/
def testNarrowShl : Except String Unit := do
  let some circ := lowerFunctionForTestV1 narrowShlFn false |>.toOption | throw "narrowShl failed"
  unless circ.assertions.any (fun a => a.message == "u8 shl overflow") do
    throw "narrowShl should assert u8 shl overflow"

elab "#pf_psy_narrow_guard" : command => do
  let results := #[testNarrowAdd, testNarrowSub, testNarrowDiv, testNarrowShl]
  for r in results do
    match r with
    | .ok () => pure ()
    | .error e =>
        throwError s!"R-HARD narrow guard failed: {e}"

#pf_psy_narrow_guard

end Tests.PsyNarrow