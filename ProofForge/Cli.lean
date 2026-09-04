/-
  `pf` — ProofForge Psy compiler CLI.

  Psy counterpart of the EVM CLI (`ProofForge.Cli` in ProofForgeEvm):
  `pf build [--out DIR] [--module MOD] [Contract ...]` extracts `@[pf_entry]`
  modules, lowers them to the validated Psy Plan, and writes the canonical
  DPN package JSON per contract (`Name.dpn.json`).

  This build of pf supports the Psy target only.
-/
import Lean
import ProofForge.Extract
import ProofForge.Core.IR
import ProofForge.Psy.Emit
import ProofForge.Psy.Registry

namespace ProofForge.Cli

inductive Command where
  | build
  | init
  deriving BEq, Repr, Inhabited

structure Options where
  command : Command := .build
  outDir : System.FilePath := "build/out"
  names : Array String := #[]
  /-- Fully-qualified Lean modules (`MyContract.Counter`). Overrides in-tree fixture mapping when set. -/
  modules : Array String := #[]
  /-- Project directory name for `pf init`. -/
  initName : String := ""
  help : Bool := false
  version : Bool := false

private def usage : String :=
  "pf — ProofForge Psy compiler\n" ++
    "\n" ++
    "Usage:\n" ++
    "  pf build [--out DIR] [--module MOD] [Contract ...]\n" ++
    "  pf init <name>\n" ++
    "  pf --version\n" ++
    "\n" ++
    "build writes Name.dpn.json (canonical DPN package JSON)\n" ++
    "--module takes a dotted Lean module (repeatable). Bare Contract names map to in-tree Examples fixtures.\n" ++
    "User projects should pass --module or list [[program]] entries in pf.toml.\n" ++
    "No contract names on build means every registered source module.\n"

def parseArgs (args : List String) : Except String Options :=
  let rec go (rest : List String) (o : Options) : Except String Options :=
    match rest with
    | [] => .ok o
    | "-h" :: _ | "--help" :: _ => .ok { o with help := true }
    | "--version" :: _ | "-V" :: _ => .ok { o with version := true }
    | "--target" :: t :: rest =>
      if t == "psy" then go rest o
      else .error s!"unknown target {t} (this build of pf supports Psy only)"
    | "--out" :: d :: rest => go rest { o with outDir := d }
    | "--module" :: m :: rest => go rest { o with modules := o.modules.push m }
    | flag :: rest =>
      if flag.startsWith "-" then .error s!"unknown flag {flag}"
      else if o.command == .init && o.initName.isEmpty then
        go rest { o with initName := flag }
      else
        go rest { o with names := o.names.push flag }
  let args := args.dropWhile (· == "--")
  let (_cmd, rest) :=
    match args with
    | "build" :: rest => (Command.build, rest)
    | "init" :: rest => (Command.init, rest)
    | rest => (Command.build, rest)
  go rest { command := _cmd }

private def psyProgramNames : Array String :=
  Psy.Registry.names

private def selectPsyNames (names : Array String) : Except String (Array String) :=
  if names.isEmpty then .ok psyProgramNames
  else
    names.mapM fun n =>
      match psyProgramNames.find? (· == n) with
      | some _ => .ok n
      | none => .error s!"unknown psy program {n}"

/-- Psy fixtures live at `Examples.Psy.<Name>`; shared fixtures at `Examples.<Name>`. -/
def fixtureModule (name : String) : Lean.Name :=
  Lean.Name.str `Examples.Psy name

structure BuildUnit where
  name : String
  module : Lean.Name
  deriving Repr

private def dottedToName (mod : String) : Lean.Name :=
  (mod.splitOn ".").foldl (fun n p => if p.isEmpty then n else Lean.Name.str n p) .anonymous

private def basenameOfModule (mod : String) : String :=
  match (mod.splitOn ".").getLast? with
  | some n => n
  | none => mod

private def trimStr (s : String) : String :=
  s.trimAscii.toString

private def dropStr (s : String) (n : Nat) : String :=
  (s.drop n).toString

private def dropEndStr (s : String) (n : Nat) : String :=
  (s.dropEnd n).toString

private def unquoteToml (v0 : String) : String :=
  let v := trimStr v0
  if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
    dropEndStr (dropStr v 1) 1
  else if v.startsWith "'" && v.endsWith "'" && v.length ≥ 2 then
    dropEndStr (dropStr v 1) 1
  else v

/-- Value after the first `=` on a TOML assignment line. -/
private def tomlValue (line : String) : Option String :=
  match line.splitOn "=" with
  | _ :: rest =>
    if rest.isEmpty then none
    else some (unquoteToml (String.intercalate "=" rest))
  | _ => none

/-- Minimal `pf.toml` reader: collect `[[program]]` tables with `name` / `module`. -/
private def parsePfTomlPrograms (text : String) : Array BuildUnit := Id.run do
  let mut units : Array BuildUnit := #[]
  let mut inProgram := false
  let mut curName : Option String := none
  let mut curModule : Option String := none
  let flush (units : Array BuildUnit) (curName : Option String) (curModule : Option String) :=
    match curModule with
    | some m =>
      let n := curName.getD (basenameOfModule m)
      units.push { name := n, module := dottedToName m }
    | none => units
  for line0 in text.splitOn "\n" do
    let line := trimStr line0
    if line.isEmpty || line.startsWith "#" then
      pure ()
    else if line == "[[program]]" then
      if inProgram then
        units := flush units curName curModule
      inProgram := true
      curName := none
      curModule := none
    else if inProgram then
      if line.startsWith "name" then
        match tomlValue line with
        | some v => curName := some v
        | none => pure ()
      else if line.startsWith "module" then
        match tomlValue line with
        | some v => curModule := some v
        | none => pure ()
      else if line.startsWith "[" then
        units := flush units curName curModule
        inProgram := false
        curName := none
        curModule := none
  if inProgram then
    units := flush units curName curModule
  units

private def loadPfTomlUnits : IO (Array BuildUnit) := do
  let path : System.FilePath := "pf.toml"
  if !(← path.pathExists) then
    return #[]
  let text ← IO.FS.readFile path
  return parsePfTomlPrograms text

private def resolveUnits (opts : Options)
    (selectNames : Array String → Except String (Array String))
    (tomlUnits : Array BuildUnit) :
    Except String (Array BuildUnit) := do
  if !opts.modules.isEmpty then
    pure <| opts.modules.map fun m =>
      { name := basenameOfModule m, module := dottedToName m }
  else if !opts.names.isEmpty then
    let names ← selectNames opts.names
    pure <| names.map fun n => { name := n, module := fixtureModule n }
  else if !tomlUnits.isEmpty then
    pure tomlUnits
  else
    let names ← selectNames #[]
    pure <| names.map fun n => { name := n, module := fixtureModule n }

private def isExamplesModule : Lean.Name → Bool
  | .str .anonymous "Examples" => true
  | .str pref _ => isExamplesModule pref
  | _ => false

/--
CLI builds must re-extract IR from user modules; never emit legacy Golden smoke fixtures.
The registry only lists buildable modules and pins canonical digests for Examples fixtures.
-/
private unsafe def extractPsyPlans (units : Array BuildUnit) :
    IO (Except String (Array (String × String))) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.searchPathRef.set (← Lean.addSearchPathFromEnv (← Lean.searchPathRef.get))
    -- `lake env pf build` exports LEAN_PATH with every workspace package's
    -- build dir. Lean's import lookup short-circuits on the first entry whose
    -- module-root *directory* exists (`SearchPath.findWithExt`), so a package
    -- dir that owns sibling modules shadows a later entry that owns the
    -- exact module (e.g. `ProofForge/Attr.olean` only in proofforge-common).
    -- Resolve the transitive import closure ourselves, file-existence first,
    -- and reduce the search path to the dirs that actually supply modules.
    let envDirs : Array System.FilePath ← do
      let mut acc : Array System.FilePath := #[]
      if let some sp := ← IO.getEnv "LEAN_PATH" then
        for p in sp.splitOn ":" do
          if p.isEmpty then continue
          try acc := acc.push (← IO.FS.realPath p) catch _ => pure ()
      pure acc
    let allDirs : List System.FilePath :=
      (← Lean.searchPathRef.get) ++ envDirs.toList
    let mut visited : Std.HashSet Lean.Name := {}
    let mut queue : Array Lean.Name := units.map (·.module)
    let mut missing : Array Lean.Name := #[]
    -- Resolved artifacts: module -> (olean, ilean) real paths.
    let mut artifacts : Array (Lean.Name × System.FilePath × System.FilePath) := #[]
    repeat
      if queue.isEmpty then break
      let mod := queue[0]!
      queue := queue.drop 1
      if visited.contains mod then continue
      visited := visited.insert mod
      let mut found : Option System.FilePath := none
      for dir in allDirs do
        let olean := Lean.modToFilePath dir mod "olean"
        if ← olean.pathExists then
          found := some olean
          break
      match found with
      | none => missing := missing.push mod
      | some olean =>
        artifacts := artifacts.push (mod, olean, olean.withExtension "ilean")
        -- Walk the closure via the ilean's `directImports` (present for every
        let ilean := olean.withExtension "ilean"
        try
          let contents ← IO.FS.readFile ilean
          match Lean.Json.parse contents with
          | .error _ => pure ()
          | .ok json =>
            match json.getObjVal? "directImports" with
            | .error _ => pure ()
            | .ok imports =>
              let entries : Array Lean.Json :=
                match imports.getArr? with
                | .ok arr => arr
                | .error _ => #[]
              for entry in entries do
                let first? : Option Lean.Json :=
                  match entry.getArr? with
                  | .ok arr => arr[0]?
                  | .error _ => none
                match first? with
                | some (Lean.Json.str name) =>
                    queue := queue.push (name.toName)
                | _ => pure ()
        catch _ => pure ()
    if missing.isEmpty then
      -- Lean's import lookup (`SearchPath.findWithExt`) short-circuits on the
      -- first entry whose module-root *directory* exists, so a package dir
      -- that owns sibling modules shadows a later entry owning the exact
      -- module (e.g. `ProofForge/Attr.olean` only in proofforge-common).
      -- Materialize a merged view of the resolved closure in a private temp
      -- dir of hard copies and put it first; every needed module then resolves
      -- from that single dir.
      let mergeDir : System.FilePath :=
        ((← IO.getEnv "XDG_RUNTIME_DIR") |>.getD ((← IO.getEnv "TMPDIR") |>.getD "/tmp"))
          / "pf-psy-lean-path"
      for (mod, olean, ilean) in artifacts do
        let dst := Lean.modToFilePath mergeDir mod "olean"
        if !(← dst.parent.get!.pathExists) then
          IO.FS.createDirAll dst.parent.get!
        IO.FS.writeBinFile dst (← IO.FS.readBinFile olean)
        let ileanDst := System.FilePath.withExtension dst "ilean"
        IO.FS.writeBinFile ileanDst (← IO.FS.readBinFile ilean)
        -- Opportunistic olean parts (server / private level data) and IR data
        -- must come along or finalizeImport fails with `missing ... data file`.
        for part in ["olean.private", "olean.server", "ir"] do
          let srcPart := System.FilePath.withExtension olean part
          if ← srcPart.pathExists then
            IO.FS.writeBinFile (System.FilePath.withExtension dst part)
              (← IO.FS.readBinFile srcPart)
      Lean.searchPathRef.set (mergeDir :: allDirs)
    else
      -- Closure incomplete: keep the plain LEAN_PATH order and let Lean
      -- report the original resolution error.
      Lean.searchPathRef.set allDirs
    Lean.enableInitializersExecution
    let modules := units.map fun u => ({ module := u.module } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return units.mapM fun u =>
      match Extract.extractModuleIR env u.module none >>= Psy.Emit.planOfExtracted with
      | .error reason => .error s!"{u.name}: {reason}"
      | .ok plan =>
        if !isExamplesModule u.module then
          .ok (u.name, Psy.Emit.planDigestHex plan)
        else
          let digest := Psy.Emit.planDigestHex plan
          match Psy.Registry.digestOf u.name with
          | some expected =>
            if digest == expected then .ok (u.name, digest)
            else .error s!"{u.name}: ir/mismatch: extracted psy digest {digest} != fixture {expected}"
          | none => .ok (u.name, digest)
  catch e =>
    return .error s!"source import failed: {e}"

private def runInit (opts : Options) : IO UInt32 := do
  if opts.initName.isEmpty then
    IO.eprintln "pf: init wants a project name"
    return 1
  let dst : System.FilePath := opts.initName
  if ← dst.pathExists then
    IO.eprintln s!"pf: refusing to overwrite {dst}"
    return 1
  let src : System.FilePath := "templates/psy-counter"
  if !(← src.pathExists) then
    IO.eprintln s!"pf: template missing at {src} (pf init is not shipped in this checkout yet)"
    return 1
  let proc ← IO.Process.output { cmd := "cp", args := #["-R", toString src, toString dst] }
  if proc.exitCode != 0 then
    IO.eprintln s!"pf: cp failed\n{proc.stderr}"
    return 1
  -- Rewrite template `require … from ".."` (templates/* → repo root).
  let lakefile := dst / "lakefile.lean"
  if ← lakefile.pathExists then
    let repoRoot ← IO.currentDir
    let dstAbs ←
      try
        IO.FS.realPath dst
      catch _ =>
        pure (repoRoot / dst)
    let parentAbs ←
      match dstAbs.parent with
      | some p =>
        try IO.FS.realPath p catch _ => pure p
      | none => pure dstAbs
    let requireFrom :=
      if parentAbs == repoRoot then ".."
      else repoRoot.toString
    let old ← IO.FS.readFile lakefile
    let rewritten :=
      old.replace "from \"..\" / \"..\"" s!"from \"{requireFrom}\""
        |>.replace "from \"../..\"" s!"from \"{requireFrom}\""
    IO.FS.writeFile lakefile rewritten
  IO.println s!"initialized {dst} (target=psy)"
  IO.println s!"next: cd {dst} && lake build && lake env pf build"
  IO.println s!"  (run `lake build pf` from the ProofForge Psy checkout; put `.lake/build/bin` on PATH)"
  return 0

private def printVersion : IO Unit := do
  IO.println "pf 0.0.1 (ProofForge Psy)"
  IO.println s!"lean {Lean.versionString}"
  IO.println "target: psy-dpn-v1 (canonical DPN package JSON)"

unsafe def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error reason =>
    IO.eprintln s!"pf: {reason}"
    IO.eprintln usage
    return 1
  | .ok opts =>
    if opts.help then
      IO.println usage
      return 0
    if opts.version then
      printVersion
      return 0
    match opts.command with
    | .init => runInit opts
    | .build =>
      let tomlUnits ← loadPfTomlUnits
      match resolveUnits opts selectPsyNames tomlUnits with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok units =>
        match ← extractPsyPlans units with
        | .error reason =>
          IO.eprintln s!"pf: {reason}"
          return 1
        | .ok _ =>
          -- Re-import once more to emit (plans and JSON come from the same
          -- env). The search path was already reduced to the merged view by
          -- extractPsyPlans; only the sysroot init is idempotent-repeated.
          try
            Lean.enableInitializersExecution
            let modules := units.map fun u => ({ module := u.module } : Lean.Import)
            let env ← Lean.importModules modules {} (loadExts := true)
            IO.FS.createDirAll opts.outDir
            for u in units do
              match (Extract.extractModuleIR env u.module >>= Psy.Emit.planOfExtracted) >>= Psy.Emit.emitPackageJsonOfPlan with
              | .error reason =>
                IO.eprintln s!"pf: {u.name}: {reason}"
                return 1
              | .ok json =>
                let path := opts.outDir / s!"{u.name}.dpn.json"
                IO.FS.writeFile path json
                IO.println s!"wrote {path} ({json.length} bytes)"
            return 0
          catch e =>
            IO.eprintln s!"pf: source import failed: {e}"
            return 1

end ProofForge.Cli

unsafe def main (args : List String) : IO UInt32 :=
  ProofForge.Cli.run args