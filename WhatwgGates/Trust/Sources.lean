import WhatwgGates.Trust.Environment

/-!
# Gates.Trust.Sources

The audited sources of the trust gate and the module-closure rule (step 1 of
section 3 of `test/contracts/trust-gate-hardening.contract.md`, and rule 5 of
addendum V2c, its reverse direction).

The audited sources are every `.lean` file under `Whatwg/`, `WhatwgTest/`,
`WhatwgGates/` and `whatwgbin/`, read from the file system, and the three roots.
The closure rule compares them with the module names of the environment the
host hands in, by exact case-sensitive path.
-/

namespace Gates.Trust

open Lean

def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "Whatwg.lean").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "Whatwg axiom gate: could not locate the project root"
  throw <| IO.userError "Whatwg axiom gate: project-root search exceeded 64 parents"

/-- The gate's own source as an absolute path. `lake build` hands the
elaborator an absolute file name; `lake env lean WhatwgTest.lean` hands it the
relative one, whose parent walk ends before the root. A relative name is joined
to the working directory first (contract section 11). -/
def absoluteSourcePath (named : System.FilePath) : IO System.FilePath := do
  if named.isAbsolute then
    return named
  return (← IO.currentDir) / named

/-- A path compared as the gate compares paths: exactly, after
`System.FilePath.normalize`, which only fixes the drive letter and the
separators, so the comparison is case-sensitive on every host (rule 5). -/
def pathKey (path : System.FilePath) : String :=
  path.normalize.toString

/-- Whether a file is a Lean source: its extension is `lean` in any case. A
host whose file system ignores case builds `X.LEAN` as module `X`, so such a
file is scanned and then refused by the exact path comparisons of the module
closure, never skipped. -/
def isLeanSourceName (path : System.FilePath) : Bool :=
  match path.extension with
  | some extension => extension.toLower == "lean"
  | none => false

def leanFilesBelow (directory : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← directory.walkDir
  return (entries.filter isLeanSourceName).qsort
    fun left right => left.toString < right.toString

/-- The audited sources: module sources, which the test root must import, and
executable entry points under `whatwgbin/`, which no audit root imports and
which the source passes alone read. -/
structure AuditedSources where
  modules : Array System.FilePath
  entryPoints : Array System.FilePath

def auditedSources (projectRoot : System.FilePath) : IO AuditedSources := do
  let production ← leanFilesBelow (projectRoot / "Whatwg")
  let tests ← leanFilesBelow (projectRoot / "WhatwgTest")
  let tooling ← leanFilesBelow (projectRoot / "WhatwgGates") -- R-V3(c), 2026-10-01
  let entryPoints ← leanFilesBelow (projectRoot / "whatwgbin") -- R-V3(c), 2026-10-01
  let roots :=
    #[projectRoot / "Whatwg.lean", projectRoot / "WhatwgGates.lean", projectRoot / "WhatwgTest.lean"] -- R-V3(c), 2026-10-01
  return { modules := production ++ tests ++ tooling ++ roots, entryPoints }

/-! ## The closure rule -/

/-- Pass 1: every module source is imported by the test root, and (rule 5 of
addendum V2c) every environment module under an audited prefix maps, by exact
case-sensitive path, to exactly one scanned module source. -/
def closureFindings (config : Config) (environment : Environment)
    (projectRoot sourceFile : System.FilePath) (sources : AuditedSources) : Array String :=
  Id.run do
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    pathKey (Lean.modToFilePath projectRoot moduleName "lean")
  let mut findings : Array String := #[]
  for source in sources.modules do
    if pathKey source != pathKey sourceFile && !importedPaths.contains (pathKey source) then
      findings := findings.push
        s!"Whatwg module-closure gate: {source.toString} is not reachable from the WhatwgTest audit root"
  let scannedPaths := sources.modules.map pathKey
  for moduleName in environment.header.moduleNames do
    if (treeOf? config moduleName).isNone then continue
    let path := pathKey (Lean.modToFilePath projectRoot moduleName "lean")
    let matching := (scannedPaths.filter (· == path)).size
    if matching == 0 then
      findings := findings.push
        s!"Whatwg module-closure gate: module {moduleName} is in the environment under an audited prefix but maps to no scanned source; its exact path would be {path}"
    else if matching != 1 then
      findings := findings.push
        s!"Whatwg module-closure gate: module {moduleName} is in the environment under an audited prefix and maps to {matching} scanned sources at {path}; exactly one is required"
  return findings

end Gates.Trust
