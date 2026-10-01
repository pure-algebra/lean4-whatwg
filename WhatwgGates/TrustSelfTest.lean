import WhatwgGates.Common

/-!
# Gates.TrustSelfTest

Exercises the elaboration-time trust gate in `WhatwgTest/Audit/AxiomGate.lean`
by planting declarations it must reject and confirming it rejects them for
the stated reason.

The gate runs in the root aggregator `WhatwgTest.lean`, which Lake
builds last. Any earlier module that fails to build prevents the gate from
running at all, so a red tree would make the planted checks meaningless. The
breaker/builder discipline deliberately keeps frozen batteries red before
their builder lands. This self-test therefore:

1. copies the Lean sources into a throwaway directory;
2. builds once and requires the set of failing modules to equal the declared
   set in `test/fixtures/trust-gate/known-red.txt`, in both directions;
3. excises the declared red modules from the copy; and
4. runs the planted-declaration checks against a genuinely green tree.

Run `lake exe whatwg_trustselftest` from anywhere inside the checkout. It invokes
`lake build` in the throwaway copy through the same toolchain.

The plants whose labels begin `V2-` are frozen by
`test/contracts/trust-gate-hardening.contract.md` (rulings R-V1 and R-V2). A
plant is a list of edits to the probe copy, undone together after its build:
append a fixture to a file (every older plant), insert one after an anchor line
the gate source carries, write one as a new module that the test root imports,
or append a comment so that Lake re-elaborates a file. After the final control
the narrow runs elaborate one file with `lake env lean` and a relative file
name, and require exit code 0 and the frozen summary text.

## Cost

The probe is seeded with the checkout's own `.lake/build` and
`.lake/packages` when they exist. Lake's traces are content hashes, not
paths, so the seeded probe replays every module that is unchanged and each
planted variant costs one incremental build of the roots it touches (a few
seconds), instead of a from-scratch build of the package and its
dependencies for the first control and a cold cache for every plant after
it. A checkout with no build directory still works; it just pays the cold
build once. The first control build doubles as the green control when no
red module is declared, so an all-green tree runs one fewer build.
-/

namespace Gates.TrustSelfTest

open Gates.Common

structure Context where
  root : System.FilePath
  probe : System.FilePath

def copiedFiles : List String :=
  ["lakefile.toml", "lake-manifest.json", "lean-toolchain",
   "Whatwg.lean", "WhatwgGates.lean", "WhatwgTest.lean"] -- R-V3(c), 2026-10-01

/-- `census` and `generated` join the copied trees because
`WhatwgTest/Audit/SpecCoverage.lean` reads the census projection and
its authored disposition inputs at elaboration time: without them the probe's
build fails for a missing file rather than for a planted violation. `vendor`
stays out: the probe only builds the census generator, never runs it. -/
def copiedTrees : List String :=
  ["Whatwg", "WhatwgTest", "WhatwgGates", "whatwgbin", "census", "generated"] -- R-V3(c), 2026-10-01

def fixture (root : System.FilePath) (name : String) : System.FilePath :=
  root / "test" / "fixtures" / "trust-gate" / name

def auditSource (probe : System.FilePath) : System.FilePath :=
  probe / "WhatwgTest" / "Audit" / "AxiomGate.lean"

def productionRoot (probe : System.FilePath) : System.FilePath :=
  probe / "Whatwg.lean"

def testRoot (probe : System.FilePath) : System.FilePath :=
  probe / "WhatwgTest.lean"

/-- A new tooling module, module `WhatwgGates.TrustSelfTestToolingPlant`. A plant in
an existing `WhatwgGates` module would make the probe re-elaborate every census
battery that imports `WhatwgGates`, and those read `vendor/` and `docs/`, which the
probe does not copy. -/
def toolingPlantModule (probe : System.FilePath) : System.FilePath :=
  probe / "WhatwgGates" / "TrustSelfTestToolingPlant.lean" -- R-V3(c), 2026-10-01

/-- A new production module under the strict prefix `Whatwg.Ecma262` of
ruling R-V1. A new leaf module is used rather than `Whatwg/Ecma262/Jobs.lean`:
the module decides strictness either way, and a plant in `Jobs.lean` would
rebuild all of `Whatwg.Streams` twice, since `Whatwg.Streams.Readable.State`
imports `Whatwg.Ecma262.Promise`, which imports `Jobs`. -/
def strictPlantModule (probe : System.FilePath) : System.FilePath :=
  probe / "Whatwg" / "Ecma262" / "TrustSelfTestPlant.lean"

/-- A new test module, module `WhatwgTest.TrustSelfTestPlant`, under no strict
prefix and under no source-token exemption. -/
def testPlantModule (probe : System.FilePath) : System.FilePath :=
  probe / "WhatwgTest" / "TrustSelfTestPlant.lean"

/-- An executable entry point under `whatwgbin/`, which no audit root imports. -/
def binEntryPoint (probe : System.FilePath) : System.FilePath :=
  probe / "whatwgbin" / "Citations.lean" -- R-V3(c), 2026-10-01

/-- The line of `WhatwgTest/Audit/AxiomGate.lean`, trimmed, after which a
strict-ceiling exception entry `⟨`Name, "reason"⟩ ::` is inserted. Frozen by
the contract; the gate carries it exactly once. -/
def strictExceptionAnchor : String :=
  "-- trust-selftest: strict-ceiling exception entries are inserted below this line"

/-- The line of `WhatwgTest/Audit/AxiomGate.lean`, trimmed, after which a
source-token exemption entry `⟨`Module, "reason"⟩ ::` is inserted. Frozen by
the contract; the gate carries it exactly once. -/
def tokenExemptionAnchor : String :=
  "-- trust-selftest: source-token exemption entries are inserted below this line"

/-- The line of `WhatwgTest/Audit/AxiomGate.lean`, trimmed, after which a
metaprogramming-module entry `⟨`Module, "reason"⟩ ::` is inserted (addendum
V2c, rule 1). Frozen by the contract; the gate carries it exactly once. -/
def metaprogrammingModuleAnchor : String :=
  "-- trust-selftest: metaprogramming-module entries are inserted below this line"

/-- The root's single gate command, before which `Placement.beforeRootGate`
inserts a fixture (addendum V2c, rule 4). -/
def rootGateCommand : String :=
  "#whatwg_streams_axiom_gate"

def copyTree (source destination : System.FilePath) : IO Unit := do
  for file in ← regularFilesBelow source do
    let relative ← relativeTo source file
    let target := destination / relative
    if let some parent := target.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile target (← IO.FS.readBinFile file)

def makeProbe (root : System.FilePath) : IO System.FilePath := do
  let base : System.FilePath ←
    match ← IO.getEnv "TMPDIR" with
    | some dir => pure dir
    | none =>
      match ← IO.getEnv "TEMP" with
      | some dir => pure dir
      | none => pure "/tmp"
  let probe := base / s!"whatwg-streams-trust-{← IO.monoNanosNow}"
  IO.FS.createDirAll probe
  for file in copiedFiles do
    IO.FS.writeBinFile (probe / file) (← IO.FS.readBinFile (root / file))
  for tree in copiedTrees do
    copyTree (root / tree) (probe / tree)
  -- Seed the probe with the checkout's build artifacts and dependency
  -- checkouts so that its builds replay instead of starting cold.
  for cached in [".lake/build", ".lake/packages"] do
    let source := root / cached
    if ← source.isDir then
      copyTree source (probe / cached)
      IO.println s!"NOTE probe seeded from {cached}"
  return probe

def lakeCommand : String :=
  if System.Platform.isWindows then "lake.exe" else "lake"

/-- Run `lake build` in the probe; return success and the combined output. -/
def build (probe : System.FilePath) : IO (Bool × String) := do
  let output ← IO.Process.output
    { cmd := lakeCommand, args := #["build"], cwd := some probe }
  return (output.exitCode == 0, output.stdout ++ output.stderr)

/-- Lake reports failing targets as `- <Module>` lines after its summary
marker. `job computation` is Lake's own pseudo-target, listed whenever any
target fails; it is never a module and is dropped. -/
def failingTargets (output : String) : List String := Id.run do
  let mut collecting := false
  let mut targets : List String := []
  for line in lines output do
    if line.startsWith "Some required targets logged failures:" then
      collecting := true
    else if collecting && line.startsWith "- " then
      let target := dropChars line 2
      if target != "job computation" then
        targets := targets ++ [target]
    else if collecting then
      collecting := false
  return targets.eraseDups.mergeSort (· < ·)

def knownRed (root : System.FilePath) : IO (List String) := do
  let path := fixture root "known-red.txt"
  unless ← path.pathExists do return []
  return (listFileEntries (← IO.FS.readFile path)).eraseDups.mergeSort (· < ·)

def moduleFile (probe : System.FilePath) (moduleName : String) : System.FilePath :=
  probe / (String.intercalate "/" (moduleName.splitOn ".") ++ ".lean")

def excise (probe : System.FilePath) (modules : List String) : IO Unit := do
  for moduleName in modules do
    let path := moduleFile probe moduleName
    unless ← path.pathExists do
      throw <| IO.userError s!"declared red module has no source file: {moduleName}"
    IO.FS.removeFile path
    IO.println s!"NOTE excised declared red module from the probe copy: {moduleName}"
  let root := testRoot probe
  let kept := (lines (← IO.FS.readFile root)).filter fun line =>
    !(modules.any fun m => line == s!"import {m}")
  IO.FS.writeFile root (String.intercalate "\n" kept ++ "\n")

def tail (output : String) (count : Nat) : String :=
  String.intercalate "\n" ((lines output).reverse.take count).reverse

/-- How a fixture enters its target file. -/
inductive Placement where
  /-- Append the fixture after a newline: the mechanism of every older plant. -/
  | append
  /-- Insert the fixture's lines after the one line whose trimmed text is the
  anchor. The edit fails, and so does its plant, when that line is absent or
  occurs more than once. -/
  | afterAnchor (anchor : String)
  /-- Write the fixture as a new module file, which must not exist yet, and put
  an `import` of it first in the test root `WhatwgTest.lean`, so that the
  module-closure gate admits it. -/
  | newModule
  /-- Append one comment line and no fixture, so that Lake re-elaborates the
  file. A plant under `bin/` needs this on the test root: the gate reads `bin/`
  at elaboration time, Lake does not track that read (debt D49), and a cached
  build would otherwise replay the earlier verdict. -/
  | reelaborate
  /-- Insert the fixture's lines immediately before the root's single
  `#whatwg_streams_axiom_gate` line (addendum V2c, plant V2c-R1). The edit
  fails, and so does its plant, when that line is absent or occurs more than
  once. The target is the root `WhatwgTest.lean`. -/
  | beforeRootGate
  deriving BEq

/-- One edit of one probe file. -/
structure Edit where
  target : System.FilePath → System.FilePath
  /-- Ignored by `Placement.reelaborate`. -/
  fixtureName : String
  placement : Placement := .append

/-- Re-elaborate `target`; see `Placement.reelaborate`. -/
def reelaborate (target : System.FilePath → System.FilePath) : Edit :=
  { target, fixtureName := "", placement := .reelaborate }

/-- Every probe file an edit writes, so that it can be restored. -/
def Edit.touched (probe : System.FilePath) (edit : Edit) : List System.FilePath :=
  if edit.placement == .newModule then [edit.target probe, testRoot probe]
  else [edit.target probe]

/-- `text` with `planted`'s lines inserted after the one line whose trimmed
text is `anchor`. Lines are rejoined with LF and a final LF. -/
def insertAfterAnchor (text anchor planted : String) : Except String String :=
  let all := lines text
  let hits := (all.filter fun line => trimmed line == anchor).length
  if hits != 1 then
    .error s!"the anchor line `{anchor}` occurs {hits} time(s); exactly one is required"
  else
    let plantedLines := lines planted
    let joined := all.foldr
      (fun line rest => if trimmed line == anchor then line :: plantedLines ++ rest else line :: rest) []
    .ok (String.intercalate "\n" joined ++ "\n")

/-- `text` with `planted`'s lines inserted immediately before the one line whose
trimmed text is `target`. Lines are rejoined with LF and a final LF. -/
def insertBeforeLine (text target planted : String) : Except String String :=
  let all := lines text
  let hits := (all.filter fun line => trimmed line == target).length
  if hits != 1 then
    .error s!"the line `{target}` occurs {hits} time(s); exactly one is required"
  else
    let plantedLines := lines planted
    let joined := all.foldr
      (fun line rest => if trimmed line == target then plantedLines ++ (line :: rest) else line :: rest) []
    .ok (String.intercalate "\n" joined ++ "\n")

/-- The module a source file under the probe defines: its relative path with
`/` read as `.` and the `.lean` extension dropped. -/
def moduleNameOf (probe path : System.FilePath) : IO String := do
  let relative ← relativeTo probe path
  unless relative.endsWith ".lean" do
    throw <| IO.userError s!"{relative} is not a Lean source"
  return String.intercalate "." ((dropLastChars relative 5).splitOn "/")

def Edit.apply (root probe : System.FilePath) (edit : Edit) : IO Unit := do
  let path := edit.target probe
  match edit.placement with
  | .append =>
    let original ← IO.FS.readBinFile path
    let planted ← IO.FS.readFile (fixture root edit.fixtureName)
    IO.FS.writeFile path (String.fromUTF8! original ++ "\n" ++ planted)
  | .afterAnchor anchor =>
    let original ← IO.FS.readFile path
    let planted ← IO.FS.readFile (fixture root edit.fixtureName)
    match insertAfterAnchor original anchor planted with
    | .ok text => IO.FS.writeFile path text
    | .error message => throw <| IO.userError s!"{path}: {message}"
  | .newModule =>
    if (← path.pathExists) then
      throw <| IO.userError s!"{path} already exists; a planted module must be new"
    IO.FS.writeFile path (← IO.FS.readFile (fixture root edit.fixtureName))
    let moduleName ← moduleNameOf probe path
    let rootText ← IO.FS.readFile (testRoot probe)
    IO.FS.writeFile (testRoot probe) (s!"import {moduleName}\n" ++ rootText)
  | .reelaborate =>
    let original ← IO.FS.readBinFile path
    IO.FS.writeFile path
      (String.fromUTF8! original ++ "\n-- trust self-test: re-elaborate this module\n")
  | .beforeRootGate =>
    let original ← IO.FS.readFile path
    let planted ← IO.FS.readFile (fixture root edit.fixtureName)
    match insertBeforeLine original rootGateCommand planted with
    | .ok text => IO.FS.writeFile path text
    | .error message => throw <| IO.userError s!"{path}: {message}"

/-- Make `edits` in order, run the block, and restore every file they wrote:
rewrite its original bytes, or remove it when it did not exist. -/
def withEdits (root probe : System.FilePath) (edits : List Edit)
    (body : IO Bool) : IO Bool := do
  let paths := (edits.flatMap (·.touched probe)).eraseDups
  let mut saved : List (System.FilePath × Option ByteArray) := []
  for path in paths do
    let original : Option ByteArray ←
      if (← path.pathExists) then do
        let bytes ← IO.FS.readBinFile path
        pure (some bytes)
      else
        pure none
    saved := saved ++ [(path, original)]
  try
    for edit in edits do
      edit.apply root probe
    body
  finally
    for (path, original) in saved do
      match original with
      | some bytes => IO.FS.writeBinFile path bytes
      | none => if (← path.pathExists) then IO.FS.removeFile path

def expectAcceptance (probe : System.FilePath) (label : String) : IO Bool := do
  let (ok, output) ← build probe
  if ok then
    IO.println s!"PASS trust gate accepted {label}"
    return true
  IO.eprintln s!"FAIL trust gate unexpectedly rejected {label}"
  IO.eprintln (tail output 60)
  return false

/-- A rejection passes when the build fails and, if `expectedFragments` is
nonempty, at least one of the fragments appears in the output. More than one
fragment is listed only where two independent layers each reject the plant
for its own stated reason and either may fire first. -/
def expectRejection (probe : System.FilePath) (label : String)
    (expectedFragments : List String) : IO Bool := do
  let (ok, output) ← build probe
  if ok then
    IO.eprintln s!"FAIL trust gate unexpectedly accepted {label}"
    return false
  match expectedFragments with
  | [] =>
    IO.println s!"PASS planted {label} rejected"
    return true
  | fragments =>
    match fragments.find? (fun fragment => (output.splitOn fragment).length > 1) with
    | some fragment =>
      IO.println s!"PASS planted {label} rejected with the expected diagnostic: {fragment}"
      return true
    | none =>
      IO.eprintln s!"FAIL trust gate rejected {label} for an unexpected reason; expected one of: {fragments}"
      IO.eprintln (tail output 60)
      return false

structure Plant where
  label : String
  fixtureName : String
  /-- Which probe file receives the fixture. -/
  target : System.FilePath → System.FilePath
  /-- Diagnostics any one of which proves the rejection is for the stated
  reason; empty means any rejection passes. -/
  expected : List String
  /-- How the fixture enters `target`. -/
  placement : Placement := .append
  /-- Further edits made with the fixture and undone with it. -/
  alsoEdits : List Edit := []

/-- The plant's edits: its own fixture first, then `alsoEdits`. -/
def Plant.edits (plant : Plant) : List Edit :=
  { target := plant.target, fixtureName := plant.fixtureName, placement := plant.placement } ::
    plant.alsoEdits

/-- Make a plant's edits and judge the build with `judge`. An edit that cannot
be made (a missing anchor, a module that already exists) fails the plant, and
the line names the plant and the reason. -/
def checkPlant (root probe : System.FilePath) (plant : Plant) (judge : IO Bool) : IO Bool := do
  try
    withEdits root probe plant.edits judge
  catch error =>
    IO.eprintln s!"FAIL could not plant {plant.label}: {error}"
    return false

def acceptancePlants : List Plant :=
  [{ label := "comments, strings, and numeric projections", fixtureName := "benign.lean.txt",
     target := auditSource, expected := [] },
   -- Rulings R-V1 and R-V2; test/contracts/trust-gate-hardening.contract.md.
   { label := "V2-A1 refused trust words in comments, documentation, strings and name literals, and identifiers that only contain them",
     fixtureName := "benign-trust-tokens.lean.txt", target := productionRoot, expected := [] },
   { label := "V2-A2 an opaque with an authored body in the production tree",
     fixtureName := "env-authored-opaque.lean.txt", target := productionRoot, expected := [] },
   { label := "V2-S2 a theorem reaching Classical.choice in a new module under WhatwgTest",
     fixtureName := "strict-choice.lean.txt", target := testPlantModule, expected := [],
     placement := .newModule }]
  -- Addendum V2b of test/contracts/trust-gate-hardening.contract.md (ruling R-V6).
  ++ [{ label := "V2b-A1 the added trust words in comments, documentation, strings and name literals, identifiers that only contain them, a local named stop, an ordinary set_option, and #guard_msgs around #check_failure",
        fixtureName := "benign-trust-tokens-v2b.lean.txt", target := productionRoot, expected := [] }]
  -- Addendum V2c of test/contracts/trust-gate-hardening.contract.md (ruling R-V10).
  ++ [{ label := "V2c-A1 the one configuration shape the tree uses, simp (config := { zetaDelta := true })",
        fixtureName := "v2c-config-control.lean.txt", target := productionRoot, expected := [] },
      { label := "V2c-A2 the new keywords and the identifier config in comments, strings, longer identifiers and an ordinary parameter",
        fixtureName := "v2c-benign.lean.txt", target := productionRoot, expected := [] }]

/-- Under the package-wide `warningAsError = true` (ruling R-6 in
`docs/SHA256-DAG.md`), Lean's own "declaration uses `sorry`" warning is
already an elaboration error, so a planted `sorry` never reaches the axiom
gate and the gate's `sorryAx` line cannot appear. Both diagnostics are
accepted for that plant: each is a rejection for the stated reason, and
which layer fires first depends on the package options, not on the plant. -/
def rejectionPlants : List Plant :=
  [{ label := "partial declaration", fixtureName := "partial.lean.txt", target := auditSource,
     expected := ["contains an authored `partial` declaration modifier"] },
   { label := "unsafe declaration", fixtureName := "unsafe.lean.txt", target := auditSource,
     expected := ["contains an authored `unsafe` declaration modifier"] },
   { label := "sorry in the production tree", fixtureName := "sorry.lean.txt",
     target := productionRoot,
     expected := ["reaches forbidden axiom sorryAx", "declaration uses `sorry`"] },
   { label := "native_decide in the production tree", fixtureName := "native-decide.lean.txt",
     target := productionRoot, expected := ["(native_decide auxiliary)"] },
   { label := "malformed string literal", fixtureName := "malformed-string.lean.txt",
     target := productionRoot, expected := [] },
   { label := "malformed raw string literal", fixtureName := "malformed-raw-string.lean.txt",
     target := productionRoot, expected := [] },
   { label := "malformed decimal literal", fixtureName := "malformed-decimal.lean.txt",
     target := productionRoot, expected := [] },
   { label := "unterminated comment", fixtureName := "malformed-comment.lean.txt",
     target := productionRoot, expected := [] },
   -- Rulings R-V1 and R-V2; test/contracts/trust-gate-hardening.contract.md.
   -- Each row below names exactly one fragment: the contract freezes which
   -- layer reports each plant, so no second layer's wording is admitted.
   -- The environment pass, in every audited tree.
   { label := "V2-E1 an axiom added through Lean.addDecl in a new test module",
     fixtureName := "env-declared-axiom.lean.txt", target := testPlantModule,
     placement := .newModule,
     expected := ["declaration plantedDeclaredAxiom is an axiom; no audited tree declares one"] },
   { label := "V2-E2 a declared axiom in the production tree",
     fixtureName := "env-production-axiom.lean.txt", target := productionRoot,
     expected := ["declaration plantedProductionAxiom is an axiom; no audited tree declares one"] },
   { label := "V2-E3 @[extern] attached through the attribute API in a new test module",
     fixtureName := "env-extern.lean.txt", target := testPlantModule, placement := .newModule,
     expected := ["declaration plantedExternTarget is `@[extern]`"] },
   { label := "V2-E4 @[implemented_by] attached through the attribute API in a new test module",
     fixtureName := "env-implemented-by.lean.txt", target := testPlantModule,
     placement := .newModule,
     expected := ["declaration plantedImplementedTarget is `@[implemented_by]`"] },
   { label := "V2-E5 @[implemented_by] under its escaped name in the production tree",
     fixtureName := "env-escaped-implemented-by.lean.txt", target := productionRoot,
     expected := ["declaration plantedEscapedTarget is `@[implemented_by]`"] },
   { label := "V2-E6 an opaque with no body in the production tree",
     fixtureName := "env-bodyless-opaque.lean.txt", target := productionRoot,
     expected := ["declaration plantedBodylessOpaque is an `opaque` with no authored body"] },
   { label := "V2-E7 a parameterised opaque with no body in a new tooling module",
     fixtureName := "env-bodyless-opaque-parameterised.lean.txt", target := toolingPlantModule,
     placement := .newModule,
     expected := ["declaration plantedParameterisedOpaque is an `opaque` with no authored body"] },
   -- The source-token pass, in commands that leave no constant behind.
   { label := "V2-T01 native_decide inside an example in the production tree",
     fixtureName := "token-native-decide.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `native_decide` trust token"] },
   { label := "V2-T02 bv_decide inside an example in a new test module",
     fixtureName := "token-bv-decide.lean.txt", target := testPlantModule,
     placement := .newModule,
     expected := ["TrustSelfTestPlant.lean contains an authored `bv_decide` trust token"] },
   { label := "V2-T03 bv_decide? inside a tactic quotation in a new test module",
     fixtureName := "token-bv-decide-query.lean.txt", target := testPlantModule,
     placement := .newModule,
     expected := ["TrustSelfTestPlant.lean contains an authored `bv_decide?` trust token"] },
   { label := "V2-T04 bv_check inside a tactic quotation in a new test module",
     fixtureName := "token-bv-check.lean.txt", target := testPlantModule,
     placement := .newModule,
     expected := ["TrustSelfTestPlant.lean contains an authored `bv_check` trust token"] },
   { label := "V2-T05 decide +native inside an example in the production tree",
     fixtureName := "token-native-flag.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `native` trust token"] },
   { label := "V2-T06 decide (native := true) inside an example in the production tree",
     fixtureName := "token-native-config.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `native` trust token"] },
   { label := "V2-T07 sorry inside an example with warningAsError switched off",
     fixtureName := "token-sorry.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `sorry` trust token"] },
   { label := "V2-T08 axiom inside a command quotation in the production tree",
     fixtureName := "token-axiom.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `axiom` trust token"] },
   { label := "V2-T09 extern inside a command quotation in the production tree",
     fixtureName := "token-extern.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `extern` trust token"] },
   { label := "V2-T10 implemented_by inside a command quotation in the production tree",
     fixtureName := "token-implemented-by.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `implemented_by` trust token"] },
   { label := "V2-T11 debug.skipKernelTC on a theorem in the production tree",
     fixtureName := "token-skip-kernel-tc.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `debug.skipKernelTC` trust token"] },
   { label := "V2-T12 the escaped spelling of debug.skipKernelTC in the production tree",
     fixtureName := "token-skip-kernel-tc-escaped.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `debug.skipKernelTC` trust token"] },
   { label := "V2-T13 the qualified spelling Lean.ofReduceBool in the production tree",
     fixtureName := "token-of-reduce-bool.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `Lean.ofReduceBool` trust token"] },
   { label := "V2-T14 the short spelling ofReduceNat under open Lean in the production tree",
     fixtureName := "token-of-reduce-nat.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `Lean.ofReduceNat` trust token"] },
   { label := "V2-T15 the spelling _root_.Lean.trustCompiler in the production tree",
     fixtureName := "token-trust-compiler.lean.txt", target := productionRoot,
     expected := ["Whatwg.lean contains an authored `Lean.trustCompiler` trust token"] },
   { label := "V2-T16 native_decide inside an example in a new tooling module",
     fixtureName := "token-native-decide.lean.txt", target := toolingPlantModule,
     placement := .newModule,
     expected := ["TrustSelfTestToolingPlant.lean contains an authored `native_decide` trust token"] },
   { label := "V2-T17 native_decide inside an example in an entry point under bin/",
     fixtureName := "token-native-decide.lean.txt", target := binEntryPoint,
     alsoEdits := [reelaborate testRoot],
     expected := ["Citations.lean contains an authored `native_decide` trust token"] },
   -- The strict ceiling of R-V1 and its exact exceptions.
   { label := "V2-S1 a theorem reaching Classical.choice in a new module under Whatwg.Ecma262",
     fixtureName := "strict-choice.lean.txt", target := strictPlantModule,
     placement := .newModule,
     expected := ["declaration TrustSelfTestPlant.plantedChoice reaches Classical.choice under the strict ceiling of Whatwg.Ecma262"] },
   { label := "V2-S3 a strict-ceiling exception naming no declaration",
     fixtureName := "strict-exception-missing.lean.txt", target := auditSource,
     placement := .afterAnchor strictExceptionAnchor,
     expected := ["strict-ceiling exception names missing declaration TrustSelfTestPlant.plantedMissing"] },
   { label := "V2-S4 a strict-ceiling exception naming a declaration that reaches no Classical.choice",
     fixtureName := "strict-exception-stale.lean.txt", target := auditSource,
     placement := .afterAnchor strictExceptionAnchor,
     alsoEdits := [{ target := strictPlantModule, fixtureName := "strict-choice-free.lean.txt",
                     placement := .newModule }],
     expected := ["stale strict-ceiling exception for TrustSelfTestPlant.plantedChoiceFree; it does not reach Classical.choice"] },
   { label := "V2-S5 a strict-ceiling exception naming a declaration under no strict prefix",
     fixtureName := "strict-exception-nonstrict.lean.txt", target := auditSource,
     placement := .afterAnchor strictExceptionAnchor,
     alsoEdits := [{ target := testPlantModule, fixtureName := "strict-choice.lean.txt",
                     placement := .newModule }],
     expected := ["stale strict-ceiling exception for TrustSelfTestPlant.plantedChoice; its module WhatwgTest.TrustSelfTestPlant is under no strict prefix"] },
   { label := "V2-S6 a strict-ceiling exception whose reason is blank",
     fixtureName := "strict-exception-unreasoned.lean.txt", target := auditSource,
     placement := .afterAnchor strictExceptionAnchor,
     alsoEdits := [{ target := strictPlantModule, fixtureName := "strict-choice.lean.txt",
                     placement := .newModule }],
     expected := ["strict-ceiling exception for TrustSelfTestPlant.plantedChoice carries no reason"] },
   -- The source-token exemption list and its staleness check.
   { label := "V2-X1 a source-token exemption for a module that names no refused token",
     fixtureName := "token-exemption-stale.lean.txt", target := auditSource,
     placement := .afterAnchor tokenExemptionAnchor,
     alsoEdits := [{ target := testPlantModule, fixtureName := "strict-choice.lean.txt",
                     placement := .newModule }],
     expected := ["stale source-token exemption for WhatwgTest.TrustSelfTestPlant; its source contains no refused token"] },
   { label := "V2-X2 a source-token exemption naming no module",
     fixtureName := "token-exemption-missing.lean.txt", target := auditSource,
     placement := .afterAnchor tokenExemptionAnchor,
     expected := ["source-token exemption names missing module WhatwgTest.TrustSelfTestPlantMissing"] }]
  -- Addendum V2b of test/contracts/trust-gate-hardening.contract.md (ruling R-V6):
  -- goal-admitting spellings and the two message switches, each fixture carrying
  -- exactly one word of the extended list, so each row names one fragment.
  ++ [{ label := "V2b-T01 sorryAx inside an example whose messages #guard_msgs drops, in the production tree",
        fixtureName := "token-sorry-ax.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `sorryAx` trust token"] },
      { label := "V2b-T02 the spelling _root_.sorryAx in the production tree",
        fixtureName := "token-sorry-ax-root.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `sorryAx` trust token"] },
      { label := "V2b-T03 the admit tactic inside an example in the production tree",
        fixtureName := "token-admit.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `admit` trust token"] },
      { label := "V2b-T04 the impossible tactic inside an example in the production tree",
        fixtureName := "token-impossible.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `impossible` trust token"] },
      { label := "V2b-T05 apply? inside an example in a new test module",
        fixtureName := "token-apply-query.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["TrustSelfTestPlant.lean contains an authored `apply?` trust token"] },
      { label := "V2b-T06 try? inside an example in a new test module",
        fixtureName := "token-try-query.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["TrustSelfTestPlant.lean contains an authored `try?` trust token"] },
      { label := "V2b-T07 grind? inside an example in a new tooling module",
        fixtureName := "token-grind-query.lean.txt", target := toolingPlantModule,
        placement := .newModule,
        expected := ["TrustSelfTestToolingPlant.lean contains an authored `grind?` trust token"] },
      { label := "V2b-T08 debug.byAsSorry on an example in the production tree",
        fixtureName := "token-by-as-sorry.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `debug.byAsSorry` trust token"] },
      { label := "V2b-T09 debug.terminalTacticsAsSorry on an example in the production tree",
        fixtureName := "token-terminal-tactics-as-sorry.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `debug.terminalTacticsAsSorry` trust token"] },
      { label := "V2b-T10 warn.sorry on an example closed by an elaborator in a new test module",
        fixtureName := "token-warn-sorry.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["TrustSelfTestPlant.lean contains an authored `warn.sorry` trust token"] },
      { label := "V2b-T11 warningAsError switched off for an example closed by grind +trace in the production tree",
        fixtureName := "token-warning-as-error.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `warningAsError` trust token"] },
      { label := "V2b-T12 the qualified spelling Lean.reduceBool inside an example in the production tree",
        fixtureName := "token-reduce-bool.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `Lean.reduceBool` trust token"] },
      { label := "V2b-T13 the short spelling reduceNat under open Lean in the production tree",
        fixtureName := "token-reduce-nat.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `Lean.reduceNat` trust token"] }]
  -- Addendum V2c of test/contracts/trust-gate-hardening.contract.md (ruling R-V10):
  -- the metaprogramming-module rule (1), token-table hygiene (2), the
  -- configuration shape (3), the root (4), and reverse closure (5). Rows that
  -- name two fragments do so where two layers each reject the plant for a stated
  -- reason and the frozen pass order leaves either able to fire first.
  ++ [{ label := "V2c-M01 a declaring metaprogramming keyword (notation) in the production tree",
        fixtureName := "v2c-meta-notation-prod.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains an authored `notation` metaprogramming keyword",
                     "module Whatwg registers a"] },
      { label := "V2c-M02 a running metaprogramming keyword (run_cmd) in a new test module",
        fixtureName := "v2c-meta-run-cmd-test.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["TrustSelfTestPlant.lean contains an authored `run_cmd` metaprogramming keyword"] },
      { label := "V2c-M03 a macro_rules that replaces the gate command, in a new test module",
        fixtureName := "v2c-meta-gate-macro-rules.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["TrustSelfTestPlant.lean contains an authored `macro_rules` metaprogramming keyword",
                     "registers a macro but is not a listed metaprogramming module",
                     "the gate command of WhatwgTest.lean did not run the gate"] },
      { label := "V2c-E01 an elaborator registered through @[command_elab], a token no source spells",
        fixtureName := "v2c-meta-attr-command-elab.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["registers an elaborator but is not a listed metaprogramming module"] },
      { label := "V2c-B1 a shadow token (native_decide hiding the word native_decide from the gate",
        fixtureName := "v2c-token-shadow-decl.lean.txt", target := testPlantModule,
        placement := .newModule,
        alsoEdits := [{ target := strictPlantModule, fixtureName := "v2c-token-shadow-use.lean.txt",
                        placement := .newModule }],
        expected := ["token `(native_decide` of the final token table is not inert",
                     "TrustSelfTestPlant.lean contains an authored `syntax` metaprogramming keyword"] },
      { label := "V2c-T1 a token that cuts a refused word short ((nat begins native)",
        fixtureName := "v2c-token-cut-word.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["token `(nat` of the final token table is not inert"] },
      { label := "V2c-T2 a token that hides a comment opener (rvV2cTok/-)",
        fixtureName := "v2c-token-comment-opener.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["of the final token table is not inert"] },
      { label := "V2c-T3 a token that hides a whole refused word (+native)",
        fixtureName := "v2c-token-hidden-native.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["token `+native` of the final token table is not inert"] },
      { label := "V2c-C1 the native flag through a config anonymous constructor in the production tree",
        fixtureName := "v2c-config-anon-ctor.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains a non-literal `config` option"] },
      { label := "V2c-C2 the native config through a { v with } record update in a new test module",
        fixtureName := "v2c-config-with.lean.txt", target := testPlantModule,
        placement := .newModule,
        expected := ["TrustSelfTestPlant.lean contains a non-literal `config` option"] },
      { label := "V2c-C3 the escaped key «config» in the production tree",
        fixtureName := "v2c-config-escaped-key.lean.txt", target := productionRoot,
        expected := ["Whatwg.lean contains a non-literal `config` option"] },
      { label := "V2c-R1 a false axiom and theorem in the root, before the gate command",
        fixtureName := "v2c-root-before-gate.lean.txt", target := testRoot,
        placement := .beforeRootGate,
        expected := ["the root WhatwgTest.lean contains a command other than imports and #whatwg_streams_axiom_gate",
                     "the root module WhatwgTest has declared a constant when the gate runs"] },
      { label := "V2c-R2 a declaration after the gate command in the root",
        fixtureName := "v2c-root-after-gate.lean.txt", target := testRoot,
        expected := ["#whatwg_streams_axiom_gate is not the last command of the root",
                     "the root WhatwgTest.lean contains a command other than imports and #whatwg_streams_axiom_gate"] },
      { label := "V2c-L1 a metaprogramming-module entry naming no module",
        fixtureName := "v2c-meta-module-missing.lean.txt", target := auditSource,
        placement := .afterAnchor metaprogrammingModuleAnchor,
        expected := ["metaprogramming-module entry names missing module WhatwgTest.TrustSelfTestPlantMissing"] },
      { label := "V2c-L2 a metaprogramming-module entry whose module declares no metaprogramming",
        fixtureName := "v2c-meta-module-stale.lean.txt", target := auditSource,
        placement := .afterAnchor metaprogrammingModuleAnchor,
        alsoEdits := [{ target := testPlantModule, fixtureName := "strict-choice.lean.txt",
                        placement := .newModule }],
        expected := ["stale metaprogramming-module entry for WhatwgTest.TrustSelfTestPlant; its source declares no syntax, macro or elaborator and registers nothing"] },
      { label := "V2c-L3 a metaprogramming-module entry whose reason is blank",
        fixtureName := "v2c-meta-module-blank.lean.txt", target := auditSource,
        placement := .afterAnchor metaprogrammingModuleAnchor,
        alsoEdits := [{ target := testPlantModule, fixtureName := "strict-choice.lean.txt",
                        placement := .newModule }],
        expected := ["metaprogramming-module entry for WhatwgTest.TrustSelfTestPlant carries no reason"] }]

/-- One narrow run: `lake env lean <file>` in the probe root, with `file`
spelled as a person types it there, relative and without a leading `./`. -/
structure NarrowRun where
  label : String
  file : String
  /-- Every template must match within one line of the output; see
  `templateMatches`. -/
  templates : List String

/-- The placeholder for a decimal numeral in a template. -/
def numeralPlaceholder : String := "<n>"

/-- The summary line of the gate frozen by the contract, counts left open. -/
def gateSummaryTemplate : String :=
  "Whatwg module and axiom gate: checked <n> source files and <n> declarations; " ++
  "Classical.choice is reached by <n> of <n> declarations in Whatwg, <n> of <n> in WhatwgTest " ++
  "and <n> of <n> in WhatwgGates; strict ceiling propext and Quot.sound over <n> module prefix(es) " ++ -- R-V3(c), 2026-10-01
  "with <n> exact exception(s); <n> source-token exemption(s)"

def narrowRuns : List NarrowRun :=
  [{ label := "V2-N1 the axiom gate run narrowly as `lake env lean WhatwgTest.lean`",
     file := "WhatwgTest.lean", templates := [gateSummaryTemplate] },
   { label := "V2-N2 the spec coverage gate run narrowly by its relative file name",
     file := "WhatwgTest/Audit/SpecCoverage.lean",
     templates := ["Whatwg spec coverage gate: <n> frozen rows agree with "] }]

/-- `text` with `pattern` removed from its front, if it starts with it. -/
def stripPrefixChars : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p == c then stripPrefixChars ps cs else none

/-- Whether `text` starts with the template whose literal pieces, between
numeral placeholders, are `pieces`. A placeholder matches one or more ASCII
digits, taken greedily; every piece after the first starts with a non-digit. -/
def matchPieces : List (List Char) → List Char → Bool
  | [], _ => true
  | [piece], text => (stripPrefixChars piece text).isSome
  | piece :: rest, text =>
    match stripPrefixChars piece text with
    | none => false
    | some after =>
      let digits := after.takeWhile Char.isDigit
      !digits.isEmpty && matchPieces rest (after.drop digits.length)

/-- Whether the template matches starting at some position of `text`. -/
def matchesSomewhere (pieces : List (List Char)) : List Char → Bool
  | [] => matchPieces pieces []
  | c :: cs => matchPieces pieces (c :: cs) || matchesSomewhere pieces cs

/-- Whether `template` matches within some line of `output`. -/
def templateMatches (template output : String) : Bool :=
  let pieces := (template.splitOn numeralPlaceholder).map String.toList
  (lines output).any fun line => matchesSomewhere pieces line.toList

/-- Lines of `output` that carry a Lean or Lake error message, all of them. -/
def errorLines (output : String) : List String :=
  (lines output).filter fun line => (line.splitOn "error:").length > 1

def expectNarrowRun (probe : System.FilePath) (narrow : NarrowRun) : IO Bool := do
  let output ← IO.Process.output
    { cmd := lakeCommand, args := #["env", "lean", narrow.file], cwd := some probe }
  let text := output.stdout ++ output.stderr
  if output.exitCode != 0 then
    IO.eprintln s!"FAIL {narrow.label}: `lake env lean {narrow.file}` exited with code {output.exitCode}"
    for line in errorLines text do IO.eprintln s!"  {line}"
    return false
  let missing := narrow.templates.filter fun template => !(templateMatches template text)
  if missing.isEmpty then
    IO.println s!"PASS {narrow.label}: exit code 0 and a line matching each of {narrow.templates}"
    return true
  IO.eprintln s!"FAIL {narrow.label}: exit code 0, but no line matches:"
  for template in missing do IO.eprintln s!"  {template}"
  IO.eprintln (tail text 60)
  return false

def run (root : System.FilePath) (probe : System.FilePath) : IO Bool := do
  -- 0. The declared red set must be exactly the failing set.
  let declared ← knownRed root
  let (_, output) ← build probe
  let observed := (failingTargets output).filter fun target =>
    !(declared.length > 0 && target == "WhatwgTest")
  if observed != declared then
    IO.eprintln "FAIL the declared red set does not match the modules that actually fail"
    IO.eprintln "--- failing but not declared in test/fixtures/trust-gate/known-red.txt ---"
    for target in observed do
      unless declared.contains target do IO.eprintln s!"  {target}"
    IO.eprintln "--- declared red but actually green; remove the stale entry ---"
    for target in declared do
      unless observed.contains target do IO.eprintln s!"  {target}"
    IO.eprintln (tail output 60)
    return false
  IO.println s!"PASS declared red set matches the observed red set ({declared.length} module(s))"
  -- 1. Excise the declared red modules.
  excise probe declared
  -- 2. Green control. With nothing declared red, the build in step 0 already
  -- accepted the unmodified tree, so it is not repeated.
  let mut allOk ←
    if declared.isEmpty then
      IO.println "PASS trust gate accepted the unmodified source tree (the step-0 build)"
      pure true
    else
      expectAcceptance probe "the unmodified source tree"
  for plant in acceptancePlants do
    let ok ← checkPlant root probe plant (expectAcceptance probe plant.label)
    allOk := allOk && ok
  -- 3. Planted rejections.
  for plant in rejectionPlants do
    let ok ← checkPlant root probe plant (expectRejection probe plant.label plant.expected)
    allOk := allOk && ok
  -- 4. Module closure: a source file not reachable from the test root.
  let unreachable := probe / "WhatwgTest" / "Planted" / "Unreachable.lean"
  IO.FS.createDirAll (probe / "WhatwgTest" / "Planted")
  IO.FS.writeFile unreachable (← IO.FS.readFile (fixture root "unreachable.lean.txt"))
  let ok ← try
      expectRejection probe "unreachable test module"
        ["is not reachable from the WhatwgTest audit root"]
    finally
      IO.FS.removeDirAll (probe / "WhatwgTest" / "Planted")
  allOk := allOk && ok
  -- 5. Final green control after every restoration.
  let ok ← expectAcceptance probe "the restored source tree"
  allOk := allOk && ok
  -- 6. Narrow runs over the restored, fully built tree.
  for narrow in narrowRuns do
    let ok ← expectNarrowRun probe narrow
    allOk := allOk && ok
  return allOk

/-- Command-line entry, invoked by `whatwgbin/TrustSelfTest.lean`. -/
def cli (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: lake exe whatwg_trustselftest" -- R-V3(c), 2026-10-01
    return 2
  let root ← Gates.Common.projectRoot
  let probe ← makeProbe root
  IO.println s!"NOTE probe copy at {probe}"
  let ok ← try
      run root probe
    finally
      IO.FS.removeDirAll probe
  if ok then
    IO.println "PASS trust self-test: every planted declaration was rejected for its stated reason, every control was accepted, and every narrow run exited 0 with its frozen summary"
    return 0
  IO.eprintln "FAIL trust self-test"
  return 1

end Gates.TrustSelfTest
