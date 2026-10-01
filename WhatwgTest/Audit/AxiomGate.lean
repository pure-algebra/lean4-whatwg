import Lean
import Lean.Util.CollectAxioms
import Whatwg
import WhatwgGates
import WhatwgGates.Trust.Gate
import WhatwgGates.TrustConfig

/-!
# Whatwg trust and axiom gate

`#whatwg_streams_axiom_gate`, the last command of the test root `WhatwgTest.lean`,
decides inside `lake build` where trust enters the repository. It reads three
things: every authored source under `Whatwg/`, `WhatwgTest/`, `WhatwgGates/` and
`whatwgbin/` with the three roots; every constant and every registration of
every audited module in the compiled environment, authored, private, auxiliary
and Lean-generated alike; and the final token table. Its behaviour is frozen by
`test/contracts/trust-gate-hardening.contract.md` (rulings R-V1 and R-V2, R-V6 in
addendum V2b, R-V10 in addendum V2c, R-W7 in addendum V2e) and falsified by
`lake exe whatwg_trustselftest`.

## The wrapper and the library

Since the factor of addendum V2e.3 (ruling R-W7(a)) this module is the thin
in-tree wrapper of the gate library `WhatwgGates/Trust/`. The library holds
every pass, in order (`Gates.Trust.runPasses`, whose module documentation in
`WhatwgGates/Trust/Gate.lean` describes each pass, the two ceilings and what
the passes read), and `WhatwgGates/TrustConfig.lean` holds this repository's
data (`Gates.TrustConfig.config`: the audited trees, the ceilings, the strict
prefixes and the three anchored lists). The library is to serve the executable
gate over built `.olean` files as well, so it reads nothing of an elaboration
context. This module holds what only the in-tree command does:

- the command `#whatwg_streams_axiom_gate` and its elaborator;
- the reads only an elaborating process can make, which it hands the library:
  the final token table (`Parser.getTokenTable` of the loaded parser extension,
  updated by `Parser.Module.updateTokens`), every scoped `.token` entry of the
  parser extension's loaded state, the constants the root module itself has
  declared (`constants.map₂`), and the axioms of each constant through
  `Lean.collectAxioms`, which reads the per-module axiom tables of the loaded
  extension `exportedAxiomsExt`; with them the root's file name and elaborated
  text;
- the printing: each finding as one error at the gate command, the summary line
  as one information message; and
- the post-command check below.

Every diagnostic is the library's text, printed verbatim, so each prints the
bytes it printed before the factor.

## The post-command check

Every pass above runs inside the elaborator of `#whatwg_streams_axiom_gate`,
so a module that replaces that command (a `macro_rules` or an `@[command_elab]`
for its syntax, or another parser for its token) would silence them all. When
this module is imported it therefore registers, with `initialize`, a linter
that runs after each command of the root and a module linter that runs after
the root's last command (addendum V2c.5). Neither is reached through the gate
command's syntax, and both act only in the root, which they recognise by its
file: the file being elaborated must be `WhatwgTest.lean` in the directory that
holds `Whatwg.lean`, compared exactly, so a plant or any other module that
imports this one is never treated as the root. After a root command of the
gate's syntax kind the linter checks that no macro and no elaborator other than
this module's is registered for that kind, so that this module's elaborator ran
it; after the root's last command the module linter checks that some top-level
command of the root was parsed as the gate command at all, which a missing
command, another parser for its token, or a wrapper such as
`#guard_msgs (drop all) in` (which would discard its verdict) breaks. When
either check fails it logs "the gate command of WhatwgTest.lean did not run the
gate" and runs every pass itself, so rule 1 names the module that replaced the
command. The check reads state that code running in the same process could
change: an initializer, a command of the root, or a replacing elaborator that
removes the linters or edits what they read is refused by rule 1 or the root
pass only when a pass runs, and otherwise by `lake exe whatwg_trustselftest`,
whose rejection rows would then all be accepted (contract V2c.7).

This module spells every refused word and every metaprogramming keyword it
does not use as a string literal, so it needs no exemption of its own; it is a
listed metaprogramming module because it declares the gate command, its
elaborator and the post-command check. Sections 13, V2b.6 and V2c.7 of the
contract state what a green gate does not mean: among others, code that runs
before the post-command check (an initializer, or a command in the root) and
removes it is invisible to the passes.
-/

open Lean

namespace WhatwgTest.Audit

/-! ## The in-tree host -/

open Elab Command

/-- Every scoped `.token` entry the parser extension's loaded state holds: the
tokens token-table hygiene adds to the final table (addendum V2c.3). -/
private def scopedTokenEntries (environment : Environment) : Array String := Id.run do
  let mut tokens : Array String := #[]
  for (_, entries) in (Parser.parserExtension.ext.getState environment).scopedEntries.map.toList do
    for entry in entries.toArray do
      if let .token token := entry then
        tokens := tokens.push token
  return tokens

/-- Every pass of the gate library, in order, over the project that holds
`sourceFile`, the file the gate command runs in, whose elaborated text is
`sourceText`. Each pass logs every finding as its own error; the summary line is
logged only when no pass has one. -/
private def runGate (sourceFile : System.FilePath) (sourceText : String) : CommandElabM Unit := do
  let environment ← getEnv
  let reads : Gates.Trust.HostReads :=
    { tokenTable := Parser.Module.updateTokens (Parser.getTokenTable environment)
      scopedTokens := scopedTokenEntries environment
      rootConstants := (environment.constants.map₂.toList.map (·.1)).toArray }
  let host : Gates.Trust.Host CommandElabM :=
    { axiomsOf := fun declaration => collectAxioms declaration
      report := fun findings => do
        for finding in findings do
          logError m!"{finding}" }
  match ← (Gates.Trust.runPasses Gates.TrustConfig.config host environment reads sourceFile
      sourceText).run with
  | .ok (some summary) => logInfo m!"{summary.line}"
  | .ok none => pure ()
  | .error message => throwError message

/-! ## The gate command and the post-command check -/

/-- The gate command, run as the last command of the root `WhatwgTest.lean`. -/
syntax "#whatwg_streams_axiom_gate" : command

/-- The syntax kind of the gate command. -/
private def gateKind : Name :=
  ``«command#whatwg_streams_axiom_gate»

/-- The gate's own elaborator: every pass, over the file the command runs in. -/
@[command_elab «command#whatwg_streams_axiom_gate»]
private def elabAxiomGate : CommandElab := fun _ => do
  let sourceFile ← liftIO <| Gates.Trust.absoluteSourcePath (System.FilePath.mk (← getFileName))
  runGate sourceFile (← getFileMap).source

/-- The file being elaborated, when it is the root: `WhatwgTest.lean` in the
directory that holds `Whatwg.lean`, compared exactly. Every other module that
imports this one, a plant included, is not the root, so the post-command check
does nothing there. -/
private def rootFile? : CommandElabM (Option System.FilePath) := do
  let sourceFile ← liftIO <| Gates.Trust.absoluteSourcePath (System.FilePath.mk (← getFileName))
  unless sourceFile.fileName == some "WhatwgTest.lean" do
    return none
  let some sourceDirectory := sourceFile.parent | return none
  try
    let projectRoot ← liftIO <| Gates.Trust.findProjectRoot sourceDirectory
    if Gates.Trust.pathKey (projectRoot / "WhatwgTest.lean") == Gates.Trust.pathKey sourceFile then
      return some sourceFile
    return none
  catch _ =>
    return none

/-- Why the gate's own elaborator did not run a command of the gate's syntax
kind, or `none` when it did: no macro is registered for that kind, and the only
command elaborator registered for it is `elabAxiomGate`. -/
private def gateReplacement? (environment : Environment) : Option String :=
  let macros := (Elab.macroAttribute.getEntries environment gateKind).map (·.declName)
  let elaborators :=
    (Elab.Command.commandElabAttribute.getEntries environment gateKind).map (·.declName)
  let owner (declaration : Name) : String :=
    match Gates.Trust.moduleOf? environment declaration with
    | some moduleName => s!"{declaration} of module {moduleName}"
    | none => s!"{declaration} of the root"
  if !macros.isEmpty then
    some s!"a macro is registered for it: {", ".intercalate (macros.map owner)}"
  else if elaborators != [``elabAxiomGate] then
    some s!"its command elaborators are {", ".intercalate (elaborators.map owner)}, not {``elabAxiomGate} alone"
  else
    none

/-- Log that the gate command of the root did not run the gate, then run every
pass, so that rule 1 names the module that replaced the command. -/
private def runReplacedGate (rootFile : System.FilePath) (reason : String) :
    CommandElabM Unit := do
  logError m!"Whatwg axiom gate: the gate command of WhatwgTest.lean did not run the gate; {reason}; the post-command check runs every pass instead"
  runGate rootFile (← getFileMap).source

/-- The linter half of the post-command check (addendum V2c.5): after each
command of the root, and for a command of the gate's syntax kind, check that
the gate's own elaborator ran it. -/
private def checkRootGateCommand (command : Syntax) : CommandElabM Unit := do
  unless command.getKind == gateKind do return
  let some rootFile ← rootFile? | return
  if let some reason := gateReplacement? (← getEnv) then
    withRef command <| runReplacedGate rootFile reason

/-- The module-linter half of the post-command check (addendum V2c.5): after
the root's last command, check that one of the root's top-level commands was
parsed as the gate command. Otherwise the command is missing, was parsed by
another parser, or is nested in another command, such as
`#guard_msgs (drop all) in`, which can discard its verdict. -/
private def checkRootCommands (commands : Array Syntax) : CommandElabM Unit := do
  let some rootFile ← rootFile? | return
  unless commands.any (·.getKind == gateKind) do
    runReplacedGate rootFile
      "no top-level command of the root was parsed as #whatwg_streams_axiom_gate"

initialize
  addLinter { name := `WhatwgTest.Audit.rootGateCommandCheck, run := checkRootGateCommand }
  addModuleLinter { name := `WhatwgTest.Audit.rootCommandsCheck, run := checkRootCommands }

end WhatwgTest.Audit
