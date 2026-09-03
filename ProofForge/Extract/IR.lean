import ProofForge.Core.Ops
import ProofForge.Core.IR
import ProofForge.Core.CFG
import ProofForge.Psy.Ops

namespace ProofForge.Extract.IR

/-- The extractor is the only layer that combines target-owned value extensions. -/
inductive ValKind where
  | psy (kind : Psy.Ops.ValKind)
  deriving BEq, Repr, Inhabited, DecidableEq

def ValKind.arity : ValKind → Nat
  | .psy kind => kind.arity

/-- Target effects stay strongly typed while sharing the extractor's recursive value type.
    Psy v1 owns no effect extensions, so this wrapper is uninhabited in practice. -/
inductive OpExt (V : Type) where
  | psy (payload : Psy.Ops.OpExt V)
  deriving BEq, Repr

abbrev Cmp := Core.Ops.Cmp
abbrev Val := Core.Ops.Val ValKind
abbrev Op := Core.Ops.Op ValKind OpExt
abbrev Evaluation := Core.Evaluation ValKind
abbrev Method := Core.IR.Method ValKind OpExt
abbrev Program := Core.IR.Program ValKind OpExt
abbrev CFG := Core.CFG.Graph ValKind OpExt

def OpExt.mapValues (_mapValue : Val → Val) : OpExt Val → OpExt Val
  | .psy payload => nomatch payload

def OpExt.values : OpExt Val → Array Val
  | .psy payload => nomatch payload

def cfgDialect : Core.CFG.Dialect ValKind OpExt where
  mapValues := OpExt.mapValues
  values := OpExt.values
  payloadEq := fun left _ => match left with | .psy payload => nomatch payload

/-- Build and optimize the shared target-neutral CFG for one extracted method. -/
def toCFG (ops : Array Op) : Except String CFG := do
  let graph ← Core.CFG.lower cfgDialect ops
  Core.CFG.optimize cfgDialect graph

def methodToCFG (method : Method) : Except String CFG := do
  let graph ←
    if method.kind == .init then Core.CFG.lowerInit cfgDialect method.ops
    else Core.CFG.lower cfgDialect method.ops
  Core.CFG.optimize cfgDialect graph

def OpExt.wellFormed : OpExt Val → Bool
  | .psy payload => nomatch payload

def Op.wellFormed (op : Op) : Bool :=
  Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Extract.IR
