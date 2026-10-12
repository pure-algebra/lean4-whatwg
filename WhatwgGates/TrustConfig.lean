import WhatwgGates.Trust.Config

/-!
# Gates.TrustConfig

This repository's data for the trust gate (addenda V2e.3 and V2e.5 of
`test/contracts/trust-gate-hardening.contract.md`, ruling R-W7(a)): the audited
trees, the two ceilings, the strict prefixes and the four exact lists, each
anchored list below the comment line after which `lake exe whatwg_trustselftest`
plants its entries. `config` is the one value the gate library reads. The
in-tree command `#whatwg_streams_axiom_gate` of `WhatwgTest/Audit/AxiomGate.lean`
hands it to every pass, and the executable gate `lake exe whatwg_trustgate`,
whose entry point `whatwgbin/TrustGate.lean` links this module, hands it the
same value, so both judge with one copy. The fourth list, the extension
allowlist, is read by the executable alone.

The module declares data only and imports only `WhatwgGates.Trust.Config`. It is
imported by `WhatwgTest.Audit.AxiomGate`, which keeps it in the test root's
import closure, and by the executable's entry point, and by nothing else: not by
the umbrella `WhatwgGates`, not by any `WhatwgGates.Trust` module and not by
anything a census battery imports (ruling R-W14(b)). An after-anchor plant
therefore rebuilds this module, the gate module and the test root and relinks
the executable, and rebuilds no census battery, which would read `vendor/` and
`docs/` that the self-test's probe does not copy. The module is audited like
every tooling module and is not a metaprogramming module.
-/

namespace Gates.TrustConfig

open Lean (Name)
open Gates.Trust

/-- The audited trees, disjoint under `Name.isPrefixOf`, which compares whole
components. The SHA-256 lane that used to be a fourth is the required `hash`
package since step 6 of `docs/HASH-PACKAGE-PLAN.md`; its own gate audits it
there, and nothing under a dependency is inspected here. -/
def auditedTrees : List Name :=
  [`Whatwg, `WhatwgTest, `WhatwgGates] -- R-V3(c), 2026-10-01

/-- Ruling R-11's ceiling, Lean's standard base, binding every audited tree. -/
def repositoryCeiling : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

/-- Ruling R-V1's strict ceiling, binding every constant whose module is under a
prefix of `strictCeilingPrefixes`. -/
def strictCeiling : List Name :=
  [``propext, ``Quot.sound]

/-- Module prefixes under the strict ceiling (ruling R-V1). A prefix joins when
its measured residue, the constants under it that reach `Classical.choice`, is
zero or wholly covered by exact exceptions the coordinator accepts as debts.
Adding a prefix is one line; the build then fails with one error per residue
declaration, which is the measurement.

The five prefixes below have zero residue at the lane V landing; `Whatwg.Streams`
joined at integration, with the R-V5 repair. `Whatwg.Html.Print` and the
`String`-borne definitions of `Whatwg.Infra.{Namespaces,Text.Scalar,Text.String}`
stay under R-11: they reach `Classical.choice` through core's `String` API.
`Whatwg.Svg` joined at slice S2 of `docs/SVG-PACKAGE-PLAN.md` (rulings SV-20 and
R-S4), at zero residue: its schema is generated data whose name lookups read a
`List Char`, and no declaration of it traverses a `String`. Since slice S10 (ruling R-S25) the
entry is its four layers `Whatwg.Svg.Data`, `Whatwg.Svg.Schema`, `Whatwg.Svg.Content` and
`Whatwg.Svg.Value`, and not `Whatwg.Svg.Geometry`: that layer computes with numbers, and under
R-11 it uses the arithmetic of core (`Rat`, `Nat.sqrt`, `grind`), whose lemmas reach
`Classical.choice`, where the strict ceiling would have it prove them again. A
prefix must lie inside the `Whatwg` tree, since R-V1 keeps `WhatwgTest` and
`WhatwgGates` under R-11, and must cover at least one audited module, so that a
misspelt prefix cannot make the strict ceiling vacuous. -/
def strictCeilingPrefixes : List Name :=
  [ `Whatwg.Ecma262
  , `Whatwg.WebIdl
  , `Whatwg.Url
  , `Whatwg.Infra.Text.Utf8
  , `Whatwg.Streams
  , `Whatwg.Signatures
  , `Whatwg.Svg.Data
  , `Whatwg.Svg.Schema
  , `Whatwg.Svg.Content
  , `Whatwg.Svg.Value
  ]

/-- Exact strict-ceiling exceptions, one declaration each, written
`` ⟨`Full.Name, "reason"⟩ :: `` on its own line below the anchor comment, where
`lake exe whatwg_trustselftest` plants its entries too. The gate refuses an
entry that names no declaration, one whose module is under no strict prefix,
one whose declaration does not reach `Classical.choice`, one with a blank
reason, and one listed twice. Empty at the V2 landing. -/
def strictCeilingExceptions : List StrictCeilingException :=
  -- trust-selftest: strict-ceiling exception entries are inserted below this line
  []

/-- Private strict-ceiling exceptions. Each must resolve to exactly one audited
declaration and then passes the same checks as `strictCeilingExceptions`.
Empty at the V2 landing. -/
def privateStrictCeilingExceptions : List PrivateStrictCeilingException :=
  []

/-- Source-token exemptions by exact module name, written
`` ⟨`Full.Module, "reason"⟩ :: `` on its own line below the anchor comment. The
gate refuses an entry that names no audited module source, one that names an
entry point under `whatwgbin/` (none can be exempted), one whose source carries
no refused word in code, one with a blank reason, and one listed twice. Empty at
the V2 landing: the gate spells its word lists as literals. -/
def sourceTokenExemptions : List SourceTokenExemption :=
  -- trust-selftest: source-token exemption entries are inserted below this line
  []

/-- Metaprogramming modules by exact module name (ruling R-V10, addendum V2c.2),
written `` ⟨`Full.Module, "reason"⟩ :: `` on its own line below the anchor
comment, where `lake exe whatwg_trustselftest` plants its entries too. The gate
refuses an entry that names no audited module source, one whose source spells no
metaprogramming keyword and whose module registers nothing, one with a blank
reason, one listed twice, and one that names an entry point under `whatwgbin/`.
It holds fourteen modules: the eight that declare a `#…` gate command, the two
constructive-contract batteries that run a receipt in `run_cmd` (both groups
since the V2c landing), since the W6 landing (ruling R-W7(b), addendum
V2d), `WhatwgTest.Audit.Freeze`, which declares the registry command
`#whatwg_freeze`, and, since the HTML package of `origin/html-h7` merged
(slice S0 of seat SVG, ruling R-S1), three of that package: the tactic
`admits` and the markup term `html!`, the first metaprogramming modules under
`Whatwg`, and the combinator shape check. A battery that only uses a listed
module's command, tactic or term registers nothing and needs no entry. The list moved here from `WhatwgTest/Audit/AxiomGate.lean` with
the factor of addendum V2e.3, entries and reasons unchanged; the gate library
lists no module of its own. -/
def metaprogrammingModules : List MetaprogrammingModule :=
  -- trust-selftest: metaprogramming-module entries are inserted below this line
  ⟨`WhatwgTest.Audit.Freeze, "declares the registry command #whatwg_freeze with syntax and command_elab"⟩ ::
  ⟨`WhatwgTest.Audit.AxiomGate, "declares this gate's command and elaborator, and its post-command linters with initialize (V2c.5)"⟩ ::
  ⟨`WhatwgTest.Audit.SpecCoverage, "declares the gate command #spec_coverage_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.CensusProfileIdentity, "declares the gate command #census_profile_identity_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.WebIdl.CensusContract, "declares the gate command #webidl_census_contract_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.WebIdl.CensusQ2Contract, "declares the gate command #webidl_census_q2_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.Ecma262.CensusContract, "declares the gate command #ecma262_census_contract_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.Ecma262.CensusQ2Contract, "declares the gate command #ecma262_census_q2_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.Ecma262.EcmarkupScanner, "declares the gate command #ecmarkup_scanner_gate with elab"⟩ ::
  ⟨`WhatwgTest.Infra.IntegerConstructiveContract, "runs receipt INFRA-INTEGER-CE-001 in run_cmd: Lean.collectAxioms over nine range proofs"⟩ ::
  ⟨`WhatwgTest.Infra.ScalarConstructiveContract, "runs receipt INFRA-SCALAR-CE-001 in run_cmd: Lean.collectAxioms over nine declarations"⟩ ::
  ⟨`Whatwg.Html.Node.Admit, "declares the tactic admits with syntax and a tactic elaborator: the auto-parameter of every generated combinator, which closes a schema obligation with Eq.refl true that the kernel then evaluates"⟩ ::
  ⟨`Whatwg.Html.Syntax.Elaborator, "declares the markup term html! with three syntax categories and a term elaborator, which builds an Element.ofRaw term whose every obligation the kernel checks"⟩ ::
  ⟨`WhatwgTest.Audit.AutoCensus, "declares the instrument command #whatwg_auto_census with syntax and command_elab: it runs a tactic on each theorem statement of a module, rolls every attempt back, and reports; no module of the tree runs it"⟩ ::
  ⟨`WhatwgTest.Audit.BankCensus, "declares the instrument command #whatwg_bank_census with syntax and command_elab: it reads the declared Aesop rule banks and the rule_sets clauses of the source text, and reports; no module of the tree runs it"⟩ ::
  ⟨`Whatwg.Auto.RuleSets, "declares the named Aesop rule banks with declare_aesop_rule_sets, which registers one environment extension and one simp extension per bank in an initializer; it declares no syntax and no elaborator, and a proof that asks for a bank is kernel-checked and audited"⟩ ::
  ⟨`WhatwgTest.Html.CombinatorShape, "runs the combinator shape check in run_cmd: reads the compiled environment for the combinator of every element row and the helper of every attribute row"⟩ ::
  []

/-- The environment extensions an audited module's built file may hold entries in
(addendum V2e.5, step 5), written `` ⟨"Printed.Name", "reason"⟩ :: `` on its own
line below the anchor comment, where `lake exe whatwg_trustselftest` plants its
entries too. An extension is named by its printed name, `toString` of the name
`ModuleData.entries` records, because a private extension's name has a numeric
component no name literal spells (fifteen below). Only the executable gate reads
the list: it refuses an entry of an audited module in an extension the list does
not name, and a list entry that names an extension no audited module holds
entries in, carries no reason, or is listed twice.

Seeded at the executable's landing with exactly the 51 extensions that hold an
entry from an audited module of the unmodified tree, as the executable reads them
with no extension loaded. The reasons fall in four classes. *Compiler metadata*
shapes compiled code only, the executables and the compiler evaluation of
`#guard` (contract V2c.7), and never a kernel declaration; the substitutions of
compiled code that do matter, `@[extern]` and `@[implemented_by]`, are the
environment pass's to refuse, and they hold no entry here. An *elaboration hint*
steers how later terms elaborate, and every declaration that results is
kernel-checked and audited by the environment and axiom passes. *Bookkeeping*
(documentation, source ranges, names, messages) changes no declaration. Four are
*read by a pass*: the parser extension, the command-elaborator attribute and the
`init` attribute, which rule 1 reads, and the per-module axiom tables, which the
in-tree command reads through `Lean.collectAxioms` and the executable never does.
A later entry needs a reason the coordinator accepts, as an exemption does.

Three entries joined when the HTML package of `origin/html-h7` merged (slice S0
of seat SVG, ruling R-S1), which makes 54: the tactic-elaborator and
term-elaborator attributes, which rule 1 reads as it reads the
command-elaborator attribute, and the attribute extension, which holds the
parser attribute of each syntax category that rule 1 reads from the parser
extension. All three are held only by the two listed modules of that package. -/
def extensionAllowlist : List ExtensionAllowlistEntry :=
  -- trust-selftest: extension-allowlist entries are inserted below this line
  ⟨"Whatwg.Mask", "proof search: the rules of the Aesop bank Whatwg.Mask of the listed module Whatwg.Auto.RuleSets; a proof asks for the bank by name, and the term the search builds is kernel-checked and audited"⟩ ::
  ⟨"«aesop_Whatwg.Mask»", "proof search: the simp lemmas of the Aesop bank Whatwg.Mask; every rewrite simp makes is a proof the kernel checks"⟩ ::
  ⟨"Whatwg.Syn", "proof search: the rules of the Aesop bank Whatwg.Syn of the listed module Whatwg.Auto.RuleSets; a proof asks for the bank by name, and the term the search builds is kernel-checked and audited"⟩ ::
  ⟨"_private.Lean.ExtraModUses.0.Lean.isExtraRevModUseExt", "bookkeeping: marks a module whose initializer its importers depend on, today the rule banks of the listed module Whatwg.Auto.RuleSets; Lean reads it to record import dependencies, and the kernel never reads it"⟩ ::
  ⟨"Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt", "compiler metadata: the dead-branch analysis's summary of each compiled function, read by the code generator only"⟩ ::
  ⟨"Lean.Compiler.LCNF.baseExt", "compiler metadata: each compiled function's LCNF body in the base phase, read by the code generator only"⟩ ::
  ⟨"Lean.Compiler.LCNF.impureSigExt", "compiler metadata: the impure-phase signature of each compiled function, read by the code generator only"⟩ ::
  ⟨"Lean.Compiler.LCNF.monoExt", "compiler metadata: each compiled function's LCNF body in the mono phase, read by the code generator only"⟩ ::
  ⟨"Lean.Compiler.LCNF.monoTypeExt", "compiler metadata: the erased type of a declaration in the mono phase, read by the code generator only"⟩ ::
  ⟨"Lean.Compiler.LCNF.specExtension", "compiler metadata: which arguments of a function the code generator specialises; compiled code only"⟩ ::
  ⟨"Lean.Compiler.inlineAttrs", "compiler metadata: inline, noinline and macro_inline marks, which steer the code generator; the kernel checks the declaration's own body"⟩ ::
  ⟨"Lean.Elab.Command.commandElabAttribute", "read by a pass: command elaborators, today the gate and freeze commands of listed metaprogramming modules; rule 1 refuses one outside the list"⟩ ::
  ⟨"Lean.Elab.Structural.eqnInfoExt", "elaboration hint: what Lean needs to state the equation lemmas of a structurally recursive definition on demand; each lemma is a kernel-checked theorem"⟩ ::
  ⟨"Lean.Elab.Tactic.tacticElabAttribute", "read by a pass: tactic elaborators, today the tactic admits of the listed module Whatwg.Html.Node.Admit; rule 1 refuses one outside the list, and a proof a tactic builds is kernel-checked and audited"⟩ ::
  ⟨"Lean.Elab.Term.elabAsElim", "elaboration hint: the elab_as_elim tag, today on the generated .elim eliminators of enumerations, which changes only how an application elaborates"⟩ ::
  ⟨"Lean.Elab.Term.termElabAttribute", "read by a pass: term elaborators, today the markup term html! of the listed module Whatwg.Html.Syntax.Elaborator; rule 1 refuses one outside the list, and a term an elaborator builds is kernel-checked and audited"⟩ ::
  ⟨"Lean.Elab.WF.eqnInfoExt", "elaboration hint: the equation-lemma data of a definition by well-founded recursion (Whatwg.Infra.Text.Order); each lemma is a kernel-checked theorem"⟩ ::
  ⟨"Lean.IR.declMapExt", "compiler metadata: each compiled function's IR, which the interpreter and the code generator run; the kernel never reads it"⟩ ::
  ⟨"Lean.Linter.deprecatedAttr", "bookkeeping: deprecated marks, today on the generated toCtorIdx aliases, which make Lean warn at a use"⟩ ::
  ⟨"Lean.Meta.Grind.grindExt", "elaboration hint: theorems and patterns registered for grind; a proof grind builds is kernel-checked and audited"⟩ ::
  ⟨"Lean.Meta.Match.Extension.extension", "elaboration hint: the matcher information of each auxiliary match function, itself a kernel-checked definition"⟩ ::
  ⟨"Lean.Meta.completionBlackListExt", "bookkeeping: names the editor hides from completion"⟩ ::
  ⟨"Lean.Meta.congrKindsExt", "elaboration hint: the argument kinds of generated congruence theorems, each a kernel-checked theorem"⟩ ::
  ⟨"Lean.Meta.funIndInfoExt", "elaboration hint: how a functional induction or fun_cases principle maps to its function; the principles are kernel-checked theorems"⟩ ::
  ⟨"Lean.Meta.instanceExtension", "elaboration hint: type class instances, which steer instance search; every term the search builds is kernel-checked"⟩ ::
  ⟨"Lean.Meta.matcherLikeExt", "compiler metadata: the generated match_on_same_ctor auxiliaries the code generator inlines like matchers"⟩ ::
  ⟨"Lean.Meta.simpExtension", "elaboration hint: simp lemmas; every rewrite simp makes is a proof the kernel checks"⟩ ::
  ⟨"Lean.Parser.parserExtension", "read by a pass: tokens, syntax kinds, categories and parsers, today of listed metaprogramming modules; rule 1 refuses one outside the list and token-table hygiene tests every token"⟩ ::
  ⟨"Lean.attributeExtension", "read by a pass: attributes made from a builder, today the parser attribute of each syntax category of the listed module Whatwg.Html.Syntax.Elaborator; rule 1 reads the category from the parser extension and refuses one outside the list"⟩ ::
  ⟨"Lean.auxRecExt", "elaboration hint: the tag on generated auxiliary recursors such as casesOn and brecOn, which are kernel-checked definitions"⟩ ::
  ⟨"Lean.backwardDefeqAttr", "elaboration hint: the backward_defeq tag on rfl theorems, which dsimp reads only under an option; a dsimp step is a proof the kernel checks"⟩ ::
  ⟨"Lean.classExtension", "elaboration hint: which structures are type classes and their output parameters, today the finite universe Whatwg.Svg.Data.Universe; instance search reads it, and every term the search builds is kernel-checked"⟩ ::
  ⟨"Lean.declRangeExt", "bookkeeping: each declaration's source range"⟩ ::
  ⟨"Lean.defeqAttr", "elaboration hint: the defeq tag on rfl theorems that dsimp may use; a dsimp step is a proof the kernel checks"⟩ ::
  ⟨"Lean.deprecatedModuleExt", "bookkeeping: one entry per module saying whether it is deprecated, which makes Lean warn at an import"⟩ ::
  ⟨"Lean.docStringExt", "bookkeeping: documentation strings"⟩ ::
  ⟨"Lean.noConfusionExt", "elaboration hint: which generated declarations are noConfusion constructions, themselves kernel-checked definitions"⟩ ::
  ⟨"Lean.projectionFnInfoExt", "elaboration hint: which definitions are structure projections, themselves kernel-checked definitions"⟩ ::
  ⟨"Lean.protectedExt", "bookkeeping: the protected mark, which only makes a name need qualification"⟩ ::
  ⟨"Lean.regularInitAttr", "read by a pass: initializers, today the post-command check of the listed module WhatwgTest.Audit.AxiomGate; rule 1 refuses one outside the list, and the executable runs none"⟩ ::
  ⟨"_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt", "elaboration hint: the tag on generated sparse casesOn auxiliaries, which are kernel-checked definitions"⟩ ::
  ⟨"_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.trivialStructureInfoExt", "compiler metadata: which structures the code generator represents by their one field"⟩ ::
  ⟨"_private.Lean.Compiler.LCNF.Specialize.0.Lean.Compiler.LCNF.Specialize.specCacheExt", "compiler metadata: the cache of functions the code generator specialised"⟩ ::
  ⟨"_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.ctorLayoutExt", "compiler metadata: constructor memory layouts, read by the code generator only"⟩ ::
  ⟨"_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt", "compiler metadata: which structures the impure phase represents by their one field"⟩ ::
  ⟨"_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTypeExt", "compiler metadata: the impure-phase type of each compiled declaration, read by the code generator only"⟩ ::
  ⟨"_private.Lean.Compiler.MetaAttr.0.Lean.metaExt", "compiler metadata: the meta mark, today on the generated _auto declarations that hold an auto-param's tactic syntax; the proof that tactic builds at a use is kernel-checked"⟩ ::
  ⟨"_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt", "bookkeeping: the package each module belongs to, one entry per module"⟩ ::
  ⟨"_private.Lean.DocString.Extension.0.Lean.moduleDocExt", "bookkeeping: module documentation"⟩ ::
  ⟨"_private.Lean.ExtraModUses.0.Lean.extraModUses", "bookkeeping: import dependencies recorded for the shake tool"⟩ ::
  ⟨"_private.Lean.Meta.Constructions.SparseCasesOn.0.Lean.Meta.sparseCasesOnInfoExt", "elaboration hint: the data of generated sparse casesOn auxiliaries, which are kernel-checked definitions"⟩ ::
  ⟨"_private.Lean.Meta.MethodSpecs.0.Lean.methodSpecsAttr", "elaboration hint: the method_specs mark on derived instances, from which Lean states specification theorems on demand, each kernel-checked"⟩ ::
  ⟨"_private.Lean.Namespace.0.Lean.namespacesExt", "bookkeeping: the namespaces a module declares"⟩ ::
  ⟨"_private.Lean.Structure.0.Lean.structureExt", "elaboration hint: the fields and parents of each structure, itself a kernel-checked inductive type"⟩ ::
  ⟨"_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt", "read by a pass: each module's own table of the axioms its declarations reach, which the in-tree command reads through Lean.collectAxioms; the executable never reads it and traverses the kernel declarations itself"⟩ ::
  ⟨"recExt", "elaboration hint: the tag on recursive definitions, which simp reads when it unfolds one"⟩ ::
  ⟨"reducibilityCore", "elaboration hint: reducible, semireducible and irreducible marks, which steer unification and instance search; the kernel ignores them"⟩ ::
  ⟨"sineQueNon", "bookkeeping: library-suggestion triggers, one entry per module"⟩ ::
  ⟨"symbolFrequency", "bookkeeping: symbol counts for library suggestions, one entry per module"⟩ ::
  []

/-- This repository's configuration of the trust gate: the one value the in-tree
command and the executable gate hand the gate library. -/
def config : Config where
  auditedTrees := auditedTrees
  repositoryCeiling := repositoryCeiling
  strictCeiling := strictCeiling
  strictCeilingPrefixes := strictCeilingPrefixes
  strictCeilingExceptions := strictCeilingExceptions
  privateStrictCeilingExceptions := privateStrictCeilingExceptions
  sourceTokenExemptions := sourceTokenExemptions
  metaprogrammingModules := metaprogrammingModules
  extensionAllowlist := extensionAllowlist

end Gates.TrustConfig
