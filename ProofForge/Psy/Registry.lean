namespace ProofForge.Psy.Registry

/-- Source program registered for Psy builds and its canonical Plan digest.
    The digest pins extractor drift: `pf build` re-checks a registered
    program's Plan digest before emitting the package. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Psy.Registry