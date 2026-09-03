import Lean

open Lean

namespace ProofForge.Attr

/-- 只标记可编译根。种类由返回类型推断。 -/
initialize pfEntryAttr : TagAttribute ←
  registerTagAttribute `pf_entry
    "mark a Lean definition as a ProofForge compile root"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_entry is not a definition"

/-- 显式允许抽出器在控制流边界 β 展开的已检查、有界 helper。 -/
initialize pfInlineAttr : TagAttribute ←
  registerTagAttribute `pf_inline
    "allow the ProofForge extractor to inline a bounded helper definition"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_inline is not a definition"

/-- Mark a compiler-owned structure or inductive as an ordinary logical contract-boundary
value. This is intentionally representation-free: the shared codec still derives and validates
its complete field/variant schema, while the target owns its wire layout. The marker exists so
reusable SDK value types under the reserved `ProofForge` namespace do not need one-off extractor
or emitter cases. -/
initialize pfBoundaryAttr : TagAttribute ←
  registerTagAttribute `pf_boundary
    "allow a compiler-owned datatype to use the generic ProofForge boundary codec"
    fun decl => do
      unless decl.toString.startsWith "ProofForge." do
        throwError "extract/unsupported: pf_boundary is reserved for compiler-owned ProofForge datatypes"
      let env ← getEnv
      match env.find? decl with
      | some (.inductInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_boundary is not a structure or inductive"

def isEntry (env : Environment) (decl : Name) : Bool :=
  pfEntryAttr.hasTag env decl

def isInline (env : Environment) (decl : Name) : Bool :=
  pfInlineAttr.hasTag env decl

def isBoundary (env : Environment) (decl : Name) : Bool :=
  pfBoundaryAttr.hasTag env decl

/-- 当前环境里、恰好挂在 `ns` 下的入口（不含子名字空间）。 -/
def entriesIn (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == ns && isEntry env n then acc.push n else acc

end ProofForge.Attr
