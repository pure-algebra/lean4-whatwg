import Lean
import Lean.Util.CollectAxioms
import Whatwg
import WhatwgGates

/-!
# Whatwg trust and axiom gate

`#whatwg_streams_axiom_gate`, the last command of the test root `WhatwgTest.lean`,
decides where trust enters the repository. It reads three things: every authored
source under `Whatwg/`, `WhatwgTest/`, `WhatwgGates/` and `whatwgbin/` with the
three roots; every constant and every registration of every audited module in
the compiled environment, authored, private, auxiliary and Lean-generated alike;
and the final token table. Its behaviour is frozen by
`test/contracts/trust-gate-hardening.contract.md` (rulings R-V1 and R-V2, R-V6 in
addendum V2b, R-V10 in addendum V2c) and falsified by
`lake exe whatwg_trustselftest`.

## Passes, in order

The gate runs its passes in the order of the contract's section 3, numbered as
there, with the checks addendum V2c.1 slots into it. Every pass runs and logs
every finding it has, one error per finding, in that order; the summary line is
logged only when no pass has a finding. The contract's section 3 admits a gate
that collects every finding, and this one must: six older plants (V2-T03,
V2-T04, V2-T08, V2-T09, V2-T10 and V2b-T10) declare a `macro` or an `elab` in a
module that is not a metaprogramming module, so rule 1 refuses each at the
environment pass, and a gate that stopped there would never print the
trust-token fragment each of those rows expects. The order still decides which
message comes first.

0. *Root pass* (V2c rule 4, before step 1). The root holds only `import` lines,
   comments, documentation and `#whatwg_streams_axiom_gate`, which is its last
   command, and the root module has declared no constant when the gate runs.
   The gate runs only in the root.
1. *Module closure.* Every module source is imported by the test root, and
   (V2c rule 5) every environment module under an audited prefix maps, by exact
   case-sensitive path, to exactly one scanned source. A file whose extension is
   `lean` in any case is scanned, so a `.LEAN` file that a case-insensitive host
   builds is reported in both directions, never skipped. `whatwgbin/` is
   excluded: its files are executable roots no audit root imports.
2. *Modifier pass.* An authored `unsafe` or `partial` keyword in code, in any
   audited source, `whatwgbin/` included, is refused; so is a source the
   tokenizer cannot read to its end. After it, as a pass of its own,
   *token-table hygiene* (V2c rule 2): every token of the final table, scoped
   entries included, that neither the `lean` binary nor an `Init` module
   declares must be inert (tests T1 to T3 of addendum V2c.3), so that no token
   hides a refused word from the source passes, whoever declared it.
3. *Environment pass.* Over every constant of an audited module, apart from a
   generated safe recursor: an `unsafe` or `partial` constant, a declared
   axiom (a native-evaluation auxiliary named as such), an `@[extern]` or
   `@[implemented_by]` constant, and an `opaque` whose value Lean synthesised.
   Then (V2c rule 1, environment half) every registration an audited module's
   entries record: a token, parser, syntax category, macro, elaborator or
   initializer, refused unless both the recording module and, when it is
   audited, the module that owns the registered declaration are listed in
   `metaprogrammingModules`.
4. *Axiom pass.* `Lean.collectAxioms` over the same constants. `sorryAx`,
   `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and every
   native-evaluation auxiliary are forbidden everywhere. Ruling R-11's ceiling,
   `propext`, `Quot.sound` and `Classical.choice`, binds every audited tree.
   Ruling R-V1's strict ceiling, `propext` and `Quot.sound` only, binds every
   constant whose module is under a prefix of `strictCeilingPrefixes`, unless an
   exact entry of `strictCeilingExceptions` or `privateStrictCeilingExceptions`
   names it; every entry is checked for need.
5. *Trust-token pass.* A token of code that carries a word of `refusedWords`,
   in any audited source, is refused unless the source's module has an exact
   entry in `sourceTokenExemptions`; every entry is checked for need. Then
   (V2c rule 1, token half) a metaprogramming keyword in code outside a listed
   module, the five checks of `metaprogrammingModules` itself, and (V2c rule 3)
   every `(config := …)` whose value is not a literal brace group without
   `with` closed by `)`.

A successful run logs one summary line with the per-tree counts of
declarations that reach `Classical.choice`; addendum V2c adds no field.

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

## Two ceilings, one structure

Before R-V1 the gate held two ceilings with the same three axioms, a
"semantic" one and an "implementation" one, and an audit-module list with a
staleness check that justified nothing once R-11 admitted `Classical.choice`
everywhere. They are collapsed: R-11's ceiling binds everything, and the strict
ceiling is the only narrower bound, chosen by module prefix and relaxed only by
exact declaration. Strictness is decided by the module `getModuleIdxFor?`
records for a constant, never by its name, so a declaration cannot leave the
strict ceiling by its namespace, and an equation lemma counts in the module
that minted it. An exception admits its own declaration and nothing else: an
excepted declaration's auxiliaries need entries of their own.

## What the passes read

The source passes are lexical. Lean's own tokenizer, with the token table of
the final environment, splits each source; comments, documentation comments,
module documentation, and every literal (string, raw string, interpolated
string, character, numeric and name literals) are not code. A keyword carries a
word when its text is the word; an identifier when its `Name`, escapes removed,
equals the word's `Name`, or, for a forbidden axiom, when its last component is
the axiom's short name. So `axioms` (the receipt command's word), `externals`
and `Foo.native` are names, and `«sorry»` is refused like `sorry`. This module
spells every refused word and every metaprogramming keyword it does not use as
a string literal and every axiom as a name literal, so it needs no exemption of
its own; it is a listed metaprogramming module because it declares the gate
command, its elaborator and the post-command check.

`Parser.testParseFile` cannot replay an already-compiled source against the
final project environment: syntax introduced by a later-imported test module
can turn an earlier ordinary identifier into a keyword. Tokenization is the
right level for the source passes, and token-table hygiene bounds what a later
module's syntax can do to that tokenization; the environment pass independently
confirms what the compiled constants and registrations are.

Sections 13, V2b.6 and V2c.7 of the contract state what a green gate does not
mean: among others, a name built by metaprogramming, an option set outside the
source, a dependency's syntax and macros, the toolchain's own non-inert base
tokens, and code that runs before the post-command check (an initializer, or a
command in the root) and removes it are invisible to these passes, and
`whatwgbin/` is read by the source passes only.

This gate began as a port of lean4-effect4's `Effect4Test/Audit/AxiomGate.lean`;
the environment pass follows that gate at `0f16828a`, as R-V2 directs.
-/

open Lean

namespace WhatwgTest.Audit

/-! ## Ceilings and their lists -/

/-- Ruling R-11's ceiling, Lean's standard base, binding every audited tree. -/
private def repositoryCeiling : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

/-- Ruling R-V1's strict ceiling, binding every constant whose module is under a
prefix of `strictCeilingPrefixes`. -/
private def strictCeiling : List Name :=
  [``propext, ``Quot.sound]

/-- A ceiling as its diagnostics spell it, on one line. -/
private def ceilingText (separator : String) (ceiling : List Name) : String :=
  separator.intercalate (ceiling.map toString)

/-- Module prefixes under the strict ceiling (ruling R-V1). A prefix joins when
its measured residue, the constants under it that reach `Classical.choice`, is
zero or wholly covered by exact exceptions the coordinator accepts as debts.
Adding a prefix is one line; the build then fails with one error per residue
declaration, which is the measurement.

The five prefixes below have zero residue at the lane V landing; `Whatwg.Streams`
joined at integration, with the R-V5 repair. `Whatwg.Html.Print` and the
`String`-borne definitions of `Whatwg.Infra.{Namespaces,Text.Scalar,Text.String}`
stay under R-11: they reach `Classical.choice` through core's `String` API. A
prefix must lie inside the `Whatwg` tree, since R-V1 keeps `WhatwgTest` and
`WhatwgGates` under R-11, and must cover at least one audited module, so that a
misspelt prefix cannot make the strict ceiling vacuous. -/
private def strictCeilingPrefixes : List Name :=
  [ `Whatwg.Ecma262
  , `Whatwg.WebIdl
  , `Whatwg.Url
  , `Whatwg.Infra.Text.Utf8
  , `Whatwg.Streams
  , `Whatwg.Signatures
  ]

/-- An exact admission of one declaration under the strict ceiling to
`Classical.choice`, with the reason the coordinator accepted it as a debt. -/
private structure StrictCeilingException where
  declaration : Name
  reason : String

/-- Exact strict-ceiling exceptions, one declaration each, written
`` ⟨`Full.Name, "reason"⟩ :: `` on its own line below the anchor comment, where
`lake exe whatwg_trustselftest` plants its entries too. The gate refuses an
entry that names no declaration, one whose module is under no strict prefix,
one whose declaration does not reach `Classical.choice`, one with a blank
reason, and one listed twice. Empty at the V2 landing. -/
private def strictCeilingExceptions : List StrictCeilingException :=
  -- trust-selftest: strict-ceiling exception entries are inserted below this line
  []

/-- A strict-ceiling exception for a private declaration, identified by its
exact owning module and its original spelling, never by Lean's private-name
counter. -/
private structure PrivateStrictCeilingException where
  owner : Name
  original : Name
  reason : String

/-- Private strict-ceiling exceptions. Each must resolve to exactly one audited
declaration and then passes the same checks as `strictCeilingExceptions`.
Empty at the V2 landing. -/
private def privateStrictCeilingExceptions : List PrivateStrictCeilingException :=
  []

/-- An exact admission of one module's source to the trust-token pass, and to
no other check, with the reason it must name a refused word in code. -/
private structure SourceTokenExemption where
  moduleName : Name
  reason : String

/-- Source-token exemptions by exact module name, written
`` ⟨`Full.Module, "reason"⟩ :: `` on its own line below the anchor comment. The
gate refuses an entry that names no audited module source, one that names an
entry point under `whatwgbin/` (none can be exempted), one whose source carries
no refused word in code, one with a blank reason, and one listed twice. Empty at
the V2 landing: this module spells its word lists as literals. -/
private def sourceTokenExemptions : List SourceTokenExemption :=
  -- trust-selftest: source-token exemption entries are inserted below this line
  []

/-- An exact admission of one audited module to rule 1 of addendum V2c, with
the reason it declares syntax, a macro or an elaborator, or runs a metaprogram.
It relaxes the metaprogramming-keyword refusal and the registration refusal for
that module and nothing else: a listed module stays bound by every trust word. -/
private structure MetaprogrammingModule where
  moduleName : Name
  reason : String

/-- Metaprogramming modules by exact module name (ruling R-V10, addendum V2c.2),
written `` ⟨`Full.Module, "reason"⟩ :: `` on its own line below the anchor
comment, where `lake exe whatwg_trustselftest` plants its entries too. The gate
refuses an entry that names no audited module source, one whose source spells no
metaprogramming keyword and whose module registers nothing, one with a blank
reason, one listed twice, and one that names an entry point under `whatwgbin/`.
It holds eleven modules: the eight that declare a `#…` gate command, the two
constructive-contract batteries that run a receipt in `run_cmd` (both groups
since the V2c landing), and, since the W6 landing (ruling R-W7(b), addendum
V2d), `WhatwgTest.Audit.Freeze`, which declares the registry command
`#whatwg_freeze`. A battery that only uses that command registers nothing and
needs no entry. -/
private def metaprogrammingModules : List MetaprogrammingModule :=
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
  []

/-- The three compiler-trust axioms. With `sorryAx` they are the axioms no
audited constant may reach, and the trust-token pass refuses all four by name. -/
private def forbiddenTrustAxioms : List Name :=
  [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- Axioms no audited constant may reach. -/
private def forbiddenAxioms : List Name :=
  ``sorryAx :: forbiddenTrustAxioms

/-- `native_decide` mints a per-declaration auxiliary axiom whose name carries a
`_native` component (Lean 4.33.1 records `t._native.native_decide.ax_1_1` for a
theorem `t`). Such an axiom is forbidden by shape, whatever declaration it
hangs off. -/
private def isNativeAuxiliaryAxiom (axiomName : Name) : Bool :=
  axiomName.anyS fun component => component == "_native"

/-- The synthesised values Lean gives an `opaque` with no body
(`default_or_ofNonempty%`, `Lean/Elab/DefView.lean`). -/
private def synthesizedOpaqueBodies : List Name :=
  [``Inhabited.default, ``Classical.ofNonempty]

/-! ## Trees, modules and declarations -/

/-- The audited trees, disjoint under `Name.isPrefixOf`, which compares whole
components. The SHA-256 lane that used to be a fourth is the required `hash`
package since step 6 of `docs/HASH-PACKAGE-PLAN.md`; its own gate audits it
there, and nothing under a dependency is inspected here. -/
private def auditedTrees : List Name :=
  [`Whatwg, `WhatwgTest, `WhatwgGates] -- R-V3(c), 2026-10-01

private def treeOf? (moduleName : Name) : Option Name :=
  auditedTrees.find? (·.isPrefixOf moduleName)

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

/-- The strict prefix a module is under: the longest that matches, if any. -/
private def strictPrefixOf? (moduleName : Name) : Option Name :=
  strictCeilingPrefixes.foldl (init := none) fun best candidate =>
    if candidate.isPrefixOf moduleName then
      match best with
      | some current => if current.getNumParts < candidate.getNumParts then some candidate else best
      | none => some candidate
    else best

/-- One constant of an audited module. -/
private structure AuditedDeclaration where
  name : Name
  moduleName : Name
  tree : Name

/-- Every constant of every audited module, read from the modules' own constant
lists rather than by materialising the whole constant map. A constant that
more than one module realises (an equation lemma that several modules unfold)
appears once, under the module `getModuleIdxFor?` records, exactly as the
environment's constant map holds it once. -/
private def auditedDeclarations (environment : Environment) :
    Except String (Array AuditedDeclaration) := do
  let header := environment.header
  if header.moduleNames.size != header.moduleData.size then
    throw s!"Whatwg trust gate: the environment records {header.moduleNames.size} module names and {header.moduleData.size} module data entries"
  let mut found : Array AuditedDeclaration := #[]
  for index in [0:header.moduleNames.size] do
    let some moduleName := header.moduleNames[index]?
      | throw s!"Whatwg trust gate: module index {index} has no name"
    let some tree := treeOf? moduleName | continue
    let some data := header.moduleData[index]?
      | throw s!"Whatwg trust gate: audited module {moduleName} has no module data"
    for name in data.constNames do
      if (environment.getModuleIdxFor? name).map (·.toNat) == some index then
        found := found.push { name, moduleName, tree }
  return found

private def isGeneratedSafeRecursor (environment : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match environment.find? sourceName with
      | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
      | none => false
      | _ => false

/-- The body under every leading `fun` binder and metadata wrapper. -/
private def lambdaBody : Expr → Expr
  | .lam _ _ body _ => lambdaBody body
  | .mdata _ inner => lambdaBody inner
  | value => value

/-- Whether an `opaque` value is the one Lean synthesised for a missing body:
its head constant, under the binders a parameterised `opaque` puts in front,
is `Inhabited.default` or `Classical.ofNonempty`. An authored body that is
literally `default` is refused with them, by design (contract section 4.1). -/
private def isSynthesizedOpaqueBody (value : Expr) : Bool :=
  match (lambdaBody value).getAppFn with
  | .const name _ => synthesizedOpaqueBodies.contains name
  | _ => false

/-- Whether a string is empty after trimming ASCII whitespace. -/
private def isBlank (text : String) : Bool :=
  text.toList.all Char.isWhitespace

/-! ## Source tokens -/

/-- A word the trust-token pass refuses (contract section 4.2). -/
private structure RefusedWord where
  /-- The word as a diagnostic prints it. -/
  printed : String
  /-- The `Name` an identifier must equal, escapes removed, to carry the word. -/
  name : Name
  /-- For a forbidden axiom, the short name: an identifier whose last component
  it is carries the word as well. -/
  lastComponent? : Option String := none

private def lastStringComponent? : Name → Option String
  | .str _ component => some component
  | _ => none

/-- A dotted spelling as a `Name`, one component per dot. -/
private def dottedName (text : String) : Name :=
  (text.splitOn ".").foldl Name.mkStr Name.anonymous

private def refusedWord (printed : String) : RefusedWord :=
  { printed, name := dottedName printed }

private def refusedAxiomWord (axiomName : Name) : RefusedWord :=
  { printed := axiomName.toString, name := axiomName,
    lastComponent? := lastStringComponent? axiomName }

/-- The words that open a trust channel no constant records (ruling R-V2), each
refused as a keyword and as an identifier: compiler evaluation (`native_decide`,
`bv_decide`, `bv_decide?`, `bv_check`, and the `native` configuration flag in
every spelling), an admitted goal, an assumption, a replaced body, a
declaration the kernel never checks, and the forbidden axioms by name.

Addendum V2b (ruling R-V6) adds the spellings by which an `example` admits a
goal once a warning switch is thrown, and the switches themselves: the tactics
`admit`, `impossible`, `apply?`, `try?` and `grind?`; the options
`debug.byAsSorry`, `debug.terminalTacticsAsSorry`, `warn.sorry` and
`warningAsError`; `sorryAx` by name; and the compiler-evaluation functions
`Lean.reduceBool` and `Lean.reduceNat`, each by its last component as the
forbidden axioms are. `stop` is not refused: the tooling tree uses it as a
local name, and Lean's own warning stops it while `warningAsError` cannot be
switched off in code. -/
private def refusedWords : List RefusedWord :=
  ["native_decide", "bv_decide", "bv_decide?", "bv_check", "native", "sorry", "axiom",
    "implemented_by", "extern", "debug.skipKernelTC", "admit", "impossible", "apply?", "try?",
    "grind?", "debug.byAsSorry", "debug.terminalTacticsAsSorry", "warn.sorry",
    "warningAsError"].map refusedWord ++
  (forbiddenAxioms ++ [``Lean.reduceBool, ``Lean.reduceNat]).map refusedAxiomWord

/-- Whether one token of code carries the word. -/
private def RefusedWord.carriedBy (word : RefusedWord) : Syntax → Bool
  | .atom _ text => text == word.printed || word.lastComponent? == some text
  | .ident _ _ name _ =>
      name == word.name ||
        (word.lastComponent?.isSome && lastStringComponent? name == word.lastComponent?)
  | _ => false

/-- The atom texts that carry a refused word: every word as printed and every
short name of the last-component shape. -/
private def refusedAtomTexts : Std.HashSet String :=
  refusedWords.foldl (init := {}) fun texts word =>
    match word.lastComponent? with
    | some component => (texts.insert word.printed).insert component
    | none => texts.insert word.printed

/-- The identifier names that carry a refused word as a whole name. -/
private def refusedIdentifierNames : Std.HashSet Name :=
  refusedWords.foldl (init := {}) fun names word => names.insert word.name

/-- The last components that carry a refused word of the last-component shape. -/
private def refusedLastComponents : Std.HashSet String :=
  refusedWords.foldl (init := {}) fun components word =>
    match word.lastComponent? with
    | some component => components.insert component
    | none => components

/-- Whether a token of code carries some refused word: exactly the disjunction of
`RefusedWord.carriedBy` over `refusedWords`, decided by set membership so that
the per-word test runs only on a token that carries one. -/
private def carriesRefusedWord : Syntax → Bool
  | .atom _ text => refusedAtomTexts.contains text
  | .ident _ _ name _ =>
      refusedIdentifierNames.contains name ||
        match lastStringComponent? name with
        | some component => refusedLastComponents.contains component
        | none => false
  | _ => false

/-- The declaration modifiers the modifier pass refuses, as keywords only:
`«unsafe»` and `«partial»` stay names. -/
private def modifierWords : List String :=
  ["unsafe", "partial"]

/-- The metaprogramming keywords of rule 1 (addendum V2c.2), refused in code
outside a listed module with the whole-name shape of section 4.2: an atom whose
text is the keyword, or an identifier whose `Name`, escapes removed, equals the
keyword's. The first group declares syntax, a macro, an elaborator or an
attribute; the second runs a metaprogram at elaboration. `local` and `scoped`
are separate atoms and stay admitted, so the prefixed forms are caught through
the keyword. Not refused: `meta`, `deriving`, `open`, `attribute`, `#guard`,
`#guard_msgs` and `#check_failure`, which the tree uses as ordinary code; and
the attribute and category names `command_elab`, `term_elab`, `tactic`, `init`,
`builtin_init` and `syntax_cat`, identifiers with ordinary uses whose
registrations the environment half refuses. -/
private def metaprogrammingKeywords : List String :=
  ["syntax", "macro", "macro_rules", "elab", "elab_rules", "notation", "infix", "infixl",
    "infixr", "prefix", "postfix", "declare_syntax_cat", "binder_predicate",
    "declare_simp_like_tactic", "simproc", "dsimproc", "simproc_decl", "dsimproc_decl",
    "builtin_simproc", "builtin_dsimproc", "builtin_simproc_decl", "builtin_dsimproc_decl",
    "register_simp_attr", "register_option", "register_builtin_option", "register_label_attr",
    "register_linter_set", "register_grind_attr", "register_sym_simp_attr",
    "register_parser_alias", "register_tactic_tag", "register_error_explanation",
    "declare_config_elab", "declare_command_config_elab",
    "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab", "#eval", "#eval!", "initialize",
    "builtin_initialize", "test_extern"]

/-- The metaprogramming keywords as atom texts. -/
private def metaprogrammingKeywordTexts : Std.HashSet String :=
  metaprogrammingKeywords.foldl (init := {}) fun texts keyword => texts.insert keyword

/-- Each metaprogramming keyword by the `Name` an identifier must equal to carry it. -/
private def metaprogrammingKeywordsByName : Std.HashMap Name String :=
  metaprogrammingKeywords.foldl (init := {}) fun byName keyword =>
    byName.insert (dottedName keyword) keyword

/-- The metaprogramming keyword one token of code carries, if any. -/
private def metaprogrammingKeywordOf? : Syntax → Option String
  | .atom _ text => if metaprogrammingKeywordTexts.contains text then some text else none
  | .ident _ _ name _ => metaprogrammingKeywordsByName.get? name
  | _ => none

/-- The one token of the gate command. -/
private def gateCommandToken : String :=
  "#whatwg_streams_axiom_gate"

/-- A position in a source, one-based in both coordinates, as diagnostics print it. -/
private structure SourcePosition where
  line : Nat
  column : Nat

/-- One refused token of one source, at a one-based line and column. -/
private structure TokenHit where
  word : String
  line : Nat
  column : Nat

private def SourcePosition.hit (position : SourcePosition) (word : String) : TokenHit :=
  { word, line := position.line, column := position.column }

/-- Run Lean's own tokenizer over one source text and fold `step` over every
token of code. Documentation comments and module documentation are syntax nodes
rather than whitespace, so Lean's own parsers consume them and their prose never
becomes tokens. Each round consumes at least one byte or ends the scan, so the
byte count bounds the rounds; a round that consumes nothing, or a source that
outlasts its rounds, is a failure, never a silent end. Returns the folded state
and, when the tokenizer stopped before the end, the diagnostic that says where. -/
private def foldCodeTokens {σ : Type} (environment : Environment) (tokenTable : Parser.TokenTable)
    (fileName input : String) (init : σ) (step : σ → Syntax → SourcePosition → σ) :
    σ × Option String := Id.run do
  let inputContext := Parser.mkInputContext input fileName
  let parserContext : Parser.ParserModuleContext :=
    { env := environment, options := {} }
  let fail (pos : String.Pos.Raw) (reason : String) : String :=
    let position := inputContext.fileMap.toPosition pos
    s!"Whatwg source trust gate: tokenization failed in {fileName}:{position.line}:{position.column + 1}: {reason}"
  let mut folded := init
  let mut state := Parser.mkParserState input
  let mut projectionEnd : Option String.Pos.Raw := none
  let rounds := input.utf8ByteSize + 1
  for _ in [0:rounds] do
    let skipped := Parser.whitespace.run inputContext parserContext tokenTable state
    if let some error := skipped.errorMsg then
      return (folded, some (fail state.pos (toString error)))
    state := skipped
    if inputContext.atEnd state.pos then
      return (folded, none)
    let start := state.pos
    let docComment := Parser.Command.docComment.fn.run
      inputContext parserContext tokenTable state
    if docComment.errorMsg.isNone then
      state := docComment.popSyntax
      projectionEnd := none
    else
      let moduleDoc := Parser.Command.moduleDoc.fn.run
        inputContext parserContext tokenTable state
      if moduleDoc.errorMsg.isNone then
        state := moduleDoc.popSyntax
        projectionEnd := none
      else
        -- Lean parses the index in `h.2.trans` and `h |>.2.trans` with
        -- `fieldIdxFn`: the ordinary number tokenizer mistakes `2.trans` for a
        -- decimal. Use the same parser only immediately after a projection dot;
        -- ordinary numerals and every tokenization error retain their usual path.
        let tokenParser :=
          if projectionEnd == some state.pos && (inputContext.get state.pos).isDigit then
            Parser.fieldIdxFn
          else
            Parser.tokenFn []
        let next := tokenParser.run inputContext parserContext tokenTable state
        if let some error := next.errorMsg then
          return (folded, some (fail state.pos (toString error)))
        let token := next.stxStack.back
        let position := inputContext.fileMap.toPosition start
        folded := step folded token { line := position.line, column := position.column + 1 }
        projectionEnd :=
          if token.isToken "." || token.isToken "|>." then token.getTailPos? else none
        state := next.popSyntax
    unless start.byteIdx < state.pos.byteIdx do
      return (folded, some (fail start "the tokenizer consumed nothing"))
  return (folded, some (fail state.pos s!"the scan did not end within {rounds} rounds"))

/-- One token of code as the configuration-shape rule reads it. -/
private inductive ShapeTag where
  | openParen
  | configKey
  | assign
  | openBrace
  | closeBrace
  | closeParen
  | withKeyword
  | other
  deriving BEq, Inhabited

/-- The key `config` is an identifier whose `Name`, escapes removed, is `config`
(so `«config»` is one too), or an atom `config` should a grammar ever make it a
keyword. -/
private def shapeTagOf : Syntax → ShapeTag
  | .atom _ "(" => .openParen
  | .atom _ ":=" => .assign
  | .atom _ "{" => .openBrace
  | .atom _ "}" => .closeBrace
  | .atom _ ")" => .closeParen
  | .atom _ "with" => .withKeyword
  | .atom _ "config" => .configKey
  | .ident _ _ name _ => if name == `config then .configKey else .other
  | _ => .other

/-- Rule 3 of addendum V2c over one source's tokens of code, given the tag of
every token and the sites, each the index of a `(` immediately followed by the
key `config` and then `:=`, with its position: the next token is `{`, the brace
group it opens contains no `with`, and the token after its matching `}` is `)`.
Every site is checked, a site inside another site's group included. Each failing
site is one finding, positioned at its `(`, whose word says which conditions
failed. -/
private def configShapeFindings (tags : Array ShapeTag) (sites : Array (Nat × SourcePosition)) :
    Array TokenHit := Id.run do
  let tagAt (index : Nat) : ShapeTag := tags[index]?.getD .other
  let mut found : Array TokenHit := #[]
  for (index, position) in sites do
    if tagAt (index + 3) != .openBrace then
      found := found.push (position.hit "the value does not open with `{`")
      continue
    let mut depth := 0
    let mut sawWith := false
    let mut closing : Option Nat := none
    for cursor in [index + 3:tags.size] do
      match tagAt cursor with
      | .openBrace => depth := depth + 1
      | .closeBrace =>
          depth := depth - 1
          if depth == 0 then
            closing := some cursor
            break
      | .withKeyword => sawWith := true
      | _ => pure ()
    let mut reasons : Array String := #[]
    if sawWith then
      reasons := reasons.push "its brace group contains `with`"
    match closing with
    | none => reasons := reasons.push "its brace group is not closed, so `)` does not follow a closing `}`"
    | some cursor =>
        if tagAt (cursor + 1) != .closeParen then
          reasons := reasons.push "`)` does not follow the closing `}`"
    unless reasons.isEmpty do
      found := found.push (position.hit ("; ".intercalate reasons.toList))
  return found

/-- What the tokenizer found in one audited source. -/
private structure SourceScan where
  source : System.FilePath
  modifiers : Array TokenHit := #[]
  trustTokens : Array TokenHit := #[]
  /-- Metaprogramming keywords of rule 1 in code. -/
  metaprogrammingKeywords : Array TokenHit := #[]
  /-- Configuration sites of rule 3 that fail the shape; the word is the reason. -/
  configShapes : Array TokenHit := #[]
  /-- Why the tokenizer stopped before the end of the source, if it did. -/
  failure? : Option String := none

/-- The state `scanSource` folds over one source's tokens of code. -/
private structure ScanState where
  modifiers : Array TokenHit := #[]
  trustTokens : Array TokenHit := #[]
  metaprogrammingKeywords : Array TokenHit := #[]
  /-- The configuration-shape tag of every token so far. -/
  shapeTags : Array ShapeTag := #[]
  /-- The position of the latest `(`. -/
  latestParen : SourcePosition := { line := 0, column := 0 }
  /-- Every `(` `config` `:=` site so far: the index of its `(`, and where it is. -/
  configSites : Array (Nat × SourcePosition) := #[]

/-- Record every modifier keyword, refused trust token and metaprogramming
keyword of one token of code, and its tag for the configuration-shape rule. -/
private def scanStep (state : ScanState) (token : Syntax) (position : SourcePosition) : ScanState :=
  let state := match modifierWords.find? (token.isToken ·) with
    | some modifier => { state with modifiers := state.modifiers.push (position.hit modifier) }
    | none => state
  let state :=
    if carriesRefusedWord token then
      refusedWords.foldl (init := state) fun state word =>
        if word.carriedBy token then
          { state with trustTokens := state.trustTokens.push (position.hit word.printed) }
        else state
    else state
  let state := match metaprogrammingKeywordOf? token with
    | some keyword =>
        { state with
          metaprogrammingKeywords := state.metaprogrammingKeywords.push (position.hit keyword) }
    | none => state
  let tag := shapeTagOf token
  let index := state.shapeTags.size
  let state :=
    if tag == .assign && index ≥ 2 && state.shapeTags[index - 1]? == some .configKey &&
        state.shapeTags[index - 2]? == some .openParen then
      { state with configSites := state.configSites.push (index - 2, state.latestParen) }
    else state
  let state := if tag == .openParen then { state with latestParen := position } else state
  { state with shapeTags := state.shapeTags.push tag }

/-- Tokenize one source with Lean's own tokenizer and record every modifier
keyword, every refused trust token, every metaprogramming keyword and every
configuration site that fails the shape, in code. -/
private def scanSource (environment : Environment) (tokenTable : Parser.TokenTable)
    (source : System.FilePath) : IO SourceScan := do
  let input ← IO.FS.readFile source
  let (state, failure?) :=
    foldCodeTokens environment tokenTable source.toString input {} scanStep
  return { source, modifiers := state.modifiers, trustTokens := state.trustTokens,
           metaprogrammingKeywords := state.metaprogrammingKeywords,
           configShapes := configShapeFindings state.shapeTags state.configSites, failure? }

/-! ## Token-table hygiene -/

/-- The whole-name words of the inert test T3: every refused word as printed and
the two modifier keywords. -/
private def inertWholeWords : List String :=
  refusedWords.map (·.printed) ++ modifierWords

/-- The last-component words of the inert test T3: the short names of the
forbidden axioms, of `sorryAx` and of the two kernel-evaluation hooks. -/
private def inertLastComponents : List String :=
  refusedWords.filterMap (·.lastComponent?)

/-- The identifier read from index `start`, as the inert test T3 reads it:
components joined by `.` when the character after the dot may begin one, up to
a character that may not continue it or the end. Returns the spelling, the index
after it, and whether exactly one `.` follows it at the very end. -/
private def readIdentifier (characters : Array Char) (start : Nat) : String × Nat × Bool :=
  Id.run do
  let mut index := start
  let mut spelling := ""
  for _ in [0:characters.size + 1] do
    match characters[index]? with
    | none => break
    | some character =>
        if spelling.isEmpty || spelling.back == '.' then
          if isIdFirst character then
            spelling := spelling.push character
            index := index + 1
          else
            break
        else if isIdRest character then
          spelling := spelling.push character
          index := index + 1
        else if character == '.' && ((characters[index + 1]?).map isIdFirst).getD false then
          spelling := spelling.push '.'
          index := index + 1
        else
          break
  let trailingDot := index + 1 == characters.size && characters[index]? == some '.'
  return (spelling, index, trailingDot)

/-- The fragments test T1 refuses inside a token, each with how a reason names it. -/
private def inertForbiddenFragments : List (String × String) :=
  [(" ", "a space"), ("\t", "a tab"), ("\r", "a carriage return"), ("\n", "a line feed"),
    ("\"", "`\"`"), ("«", "`«`"), ("»", "`»`"), ("--", "`--`"), ("/-", "`/-`"), ("-/", "`-/`")]

/-- Why a token fails the inert test of addendum V2c.3, empty when it is inert.
`splitters` are the tokens of the table that contain a character that cannot
continue an identifier: an identifier may start right after one of them. -/
private def inertFailures (splitters : Array String) (token : String) : Array String := Id.run do
  let characters := token.toList.toArray
  let continues (index : Nat) : Bool := ((characters[index]?).map isIdRest).getD false
  let mut reasons : Array String := #[]
  -- T1: whitespace, quotes, guillemets and comment delimiters.
  for (fragment, described) in inertForbiddenFragments do
    if (token.splitOn fragment).length > 1 then
      reasons := reasons.push s!"T1, it contains {described}"
  -- T2: a trailing `-` or `/`, and a character-literal opener.
  if token.endsWith "-" then
    reasons := reasons.push "T2, it ends in `-`"
  if token.endsWith "/" then
    reasons := reasons.push "T2, it ends in `/`"
  for index in [0:characters.size] do
    if characters[index]? == some '\'' then
      let opens := match index with
        | 0 => true
        | previous + 1 => !continues previous
      if opens then
        reasons := reasons.push s!"T2, the `'` at index {index} opens a character literal"
  -- T3, with T2's raw-string opener, at every identifier start.
  for index in [0:characters.size] do
    let some character := characters[index]? | continue
    unless isIdFirst character do continue
    let before := String.ofList (characters.toList.take index)
    let starts := match index with
      | 0 => true
      | previous + 1 =>
          !continues previous || splitters.any fun splitter => before.endsWith splitter
    unless starts do continue
    let (spelling, stop, trailingDot) := readIdentifier characters index
    if spelling.isEmpty then continue
    if spelling == "r" &&
        (stop == characters.size || characters[stop]? == some '#' || characters[stop]? == some '"') then
      reasons := reasons.push s!"T2, the identifier `r` at index {index} opens a raw string literal"
    if stop == characters.size || trailingDot then
      let read := if trailingDot then spelling ++ "." else spelling
      for word in inertWholeWords do
        if word.startsWith read then
          reasons := reasons.push
            s!"T3, the identifier `{read}` at index {index} reaches the end of the token and begins the refused word `{word}`"
      let lastComponent := ((read.splitOn ".").getLast?).getD read
      unless lastComponent.isEmpty do
        for component in inertLastComponents do
          if component.startsWith lastComponent then
            reasons := reasons.push
              s!"T3, the last component `{lastComponent}` of the identifier at index {index} reaches the end of the token and begins the refused component `{component}`"
    else
      if inertWholeWords.contains spelling then
        reasons := reasons.push
          s!"T3, the identifier `{spelling}` at index {index} is the refused word `{spelling}`"
      let lastComponent := ((spelling.splitOn ".").getLast?).getD spelling
      if inertLastComponents.contains lastComponent then
        reasons := reasons.push
          s!"T3, the identifier `{spelling}` at index {index} ends in the refused component `{lastComponent}`"
  return reasons

/-- The tokens of the final table, scoped entries included, that neither the
`lean` binary nor an `Init` module declares, each with the modules whose parser
entries declare it. -/
private def nonBaseTokens (environment : Environment) (finalTable : Parser.TokenTable) :
    IO (Array String × Array (String × Array Name)) := do
  let builtinTable ← Parser.builtinTokenTable.get
  let mut initDeclared : Std.HashSet String := {}
  let mut declaredBy : Std.HashMap String (Array Name) := {}
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    for entry in Parser.parserExtension.ext.getModuleEntries environment index do
      let token? : Option String := match entry with
        | .global (.token token) => some token
        | .scoped _ (.token token) => some token
        | _ => none
      if let some token := token? then
        declaredBy := declaredBy.insert token ((declaredBy.getD token #[]).push moduleName)
        if (`Init).isPrefixOf moduleName then
          initDeclared := initDeclared.insert token
  let mut table : Std.HashSet String := {}
  for token in finalTable.values do
    table := table.insert token
  for (_, entries) in (Parser.parserExtension.ext.getState environment).scopedEntries.map.toList do
    for entry in entries.toArray do
      if let .token token := entry then
        table := table.insert token
  let tokens := table.toArray.qsort (· < ·)
  let nonBase := tokens.filter fun token =>
    (builtinTable.find? token).isNone && !initDeclared.contains token
  return (tokens, nonBase.map fun token => (token, declaredBy.getD token #[]))

/-! ## Registrations -/

/-- One registration an audited module's environment entries record (rule 1 of
addendum V2c, environment half). -/
private structure Registration where
  /-- The module whose entries record the registration. -/
  moduleName : Name
  /-- What it registers, with its article, as the diagnostic prints it. -/
  kind : String
  /-- What exactly it registers. -/
  detail : String
  /-- The registered declaration, when the entry names one. -/
  declaration? : Option Name := none

/-- The (key, declaration) entries one module records in a keyed declaration
attribute, global and scoped alike. -/
private def keyedEntriesOf {γ : Type} (keyed : KeyedDeclsAttribute γ)
    (environment : Environment) (index : Nat) : Array (Name × Name) :=
  (keyed.ext.ext.getModuleEntries environment index).map fun
    | .global entry => (entry.key, entry.declName)
    | .scoped _ entry => (entry.key, entry.declName)

/-- The keyed declaration attributes whose entries register a macro or an
elaborator, with the kind a refusal names. Every elaboration hook the toolchain
keys by syntax kind counts as an elaborator: command, term, tactic and
`do`-element elaborators, and the hooks of `inductive`, quotation prechecks,
`try?`, `grind` and its simproc language; so do the pretty-printing hooks
(delaborators, unexpanders, formatters and parenthesizers), which run a
metaprogram whenever a later module prints. -/
private def keyedRegistrationReaders :
    List (String × (Environment → Nat → Array (Name × Name))) :=
  [ ("a macro", keyedEntriesOf Elab.macroAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Command.commandElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Term.termElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.tacticElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Do.doElemElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Do.controlInfoElemAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Command.inductiveElabAttr)
  , ("an elaborator", keyedEntriesOf Elab.Term.Quotation.precheckAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Try.tryTacticElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Grind.grindTacElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Grind.symSimprocElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Grind.symDSimprocElabAttribute)
  , ("an elaborator", keyedEntriesOf Elab.Tactic.Grind.symDischargerElabAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.Delaborator.delabAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.Delaborator.appUnexpanderAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.formatterAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.parenthesizerAttribute)
  , ("an elaborator", keyedEntriesOf PrettyPrinter.categoryParenthesizerAttribute)
  ]

/-- Every registration one module's entries record: the parser extension's
token, syntax kind, category and parser entries, global and scoped; every
keyed declaration attribute of `keyedRegistrationReaders`; and the `init` and
`builtin_init` attributes, which `initialize`, `builtin_initialize` and the
`register_…` commands produce, read from the module's `.olean` and `.ir`
entries alike. -/
private def registrationsOf (environment : Environment) (index : Nat) (moduleName : Name) :
    Array Registration := Id.run do
  let mut found : Array Registration := #[]
  for entry in Parser.parserExtension.ext.getModuleEntries environment index do
    let parserEntry := match entry with
      | .global parserEntry => parserEntry
      | .scoped _ parserEntry => parserEntry
    match parserEntry with
    | .token token =>
        found := found.push { moduleName, kind := "a token", detail := s!"the token `{token}`" }
    | .kind kind =>
        found := found.push { moduleName, kind := "a parser", detail := s!"the syntax kind {kind}" }
    | .category category declaration _ =>
        found := found.push
          { moduleName, kind := "a syntax category", detail := s!"the category {category}",
            declaration? := some declaration }
    | .parser category declaration _ =>
        found := found.push
          { moduleName, kind := "a parser",
            detail := s!"the parser {declaration} of category {category}",
            declaration? := some declaration }
  for (kind, reader) in keyedRegistrationReaders do
    for (key, declaration) in reader environment index do
      found := found.push
        { moduleName, kind, detail := s!"the declaration {declaration} for {key}",
          declaration? := some declaration }
  for initAttribute in [regularInitAttr, builtinInitAttr] do
    let entries := initAttribute.ext.getModuleEntries environment index ++
      initAttribute.ext.getModuleIREntries environment index
    for (declaration, _) in entries do
      found := found.push
        { moduleName, kind := "an initializer", detail := s!"the declaration {declaration}",
          declaration? := some declaration }
  -- An `.ir` entry repeats its `.olean` entry when both are loaded: keep one.
  let mut unique : Array Registration := #[]
  for registration in found do
    unless unique.any (fun seen => seen.kind == registration.kind &&
        seen.detail == registration.detail) do
      unique := unique.push registration
  return unique

/-- Every registration of every audited module. -/
private def auditedRegistrations (environment : Environment) : Array Registration := Id.run do
  let mut found : Array Registration := #[]
  for index in [0:environment.header.moduleNames.size] do
    let some moduleName := environment.header.moduleNames[index]? | continue
    if (treeOf? moduleName).isSome then
      found := found ++ registrationsOf environment index moduleName
  return found

/-! ## Sources -/

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
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
private def absoluteSourcePath (named : System.FilePath) : IO System.FilePath := do
  if named.isAbsolute then
    return named
  return (← IO.currentDir) / named

/-- A path compared as the gate compares paths: exactly, after
`System.FilePath.normalize`, which only fixes the drive letter and the
separators, so the comparison is case-sensitive on every host (rule 5). -/
private def pathKey (path : System.FilePath) : String :=
  path.normalize.toString

/-- Whether a file is a Lean source: its extension is `lean` in any case. A
host whose file system ignores case builds `X.LEAN` as module `X`, so such a
file is scanned and then refused by the exact path comparisons of the module
closure, never skipped. -/
private def isLeanSourceName (path : System.FilePath) : Bool :=
  match path.extension with
  | some extension => extension.toLower == "lean"
  | none => false

private def leanFilesBelow (directory : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← directory.walkDir
  return (entries.filter isLeanSourceName).qsort
    fun left right => left.toString < right.toString

/-- The audited sources: module sources, which the test root must import, and
executable entry points under `whatwgbin/`, which no audit root imports and
which the source passes alone read. -/
private structure AuditedSources where
  modules : Array System.FilePath
  entryPoints : Array System.FilePath

private def auditedSources (projectRoot : System.FilePath) : IO AuditedSources := do
  let production ← leanFilesBelow (projectRoot / "Whatwg")
  let tests ← leanFilesBelow (projectRoot / "WhatwgTest")
  let tooling ← leanFilesBelow (projectRoot / "WhatwgGates") -- R-V3(c), 2026-10-01
  let entryPoints ← leanFilesBelow (projectRoot / "whatwgbin") -- R-V3(c), 2026-10-01
  let roots :=
    #[projectRoot / "Whatwg.lean", projectRoot / "WhatwgGates.lean", projectRoot / "WhatwgTest.lean"] -- R-V3(c), 2026-10-01
  return { modules := production ++ tests ++ tooling ++ roots, entryPoints }

/-! ## The passes -/

open Elab Command

/-- Log every finding of one pass as its own error, and say whether there was
none. -/
private def reportFindings (findings : Array MessageData) : CommandElabM Bool := do
  for finding in findings do
    logError finding
  return findings.isEmpty

/-- One token of the root as the root pass reads it. -/
private inductive RootTag where
  | importKeyword
  | identifier
  | gateCommand
  | other
  deriving BEq, Inhabited

/-- How a diagnostic shows one token: an atom's text, an identifier's spelling,
or the text of a literal. -/
private def tokenText : Syntax → String
  | .atom _ text => text
  | .ident _ raw _ _ => raw.toString
  | .node _ kind arguments =>
      match (arguments[0]? : Option Syntax) with
      | some (Syntax.atom _ text) => text
      | _ => kind.toString
  | .missing => "<missing>"

private def rootTagOf (token : Syntax) : RootTag :=
  if token.isToken "import" then .importKeyword
  else if token.isToken gateCommandToken then .gateCommand
  else if token.isIdent then .identifier
  else .other

/-- Pass 0 over the root's tokens of code (rule 4 of addendum V2c): `import` and
a module name, any number of times, then the gate command and nothing after it. -/
private def rootShapeFindings (tokens : Array (RootTag × String × SourcePosition)) :
    Array MessageData := Id.run do
  let tagAt (index : Nat) : RootTag := (tokens[index]?.map (·.1)).getD .other
  let mut index := 0
  for _ in [0:tokens.size] do
    if tagAt index == .importKeyword && tagAt (index + 1) == .identifier then
      index := index + 2
    else
      break
  let gateIndex := (tokens.findIdx? (·.1 == RootTag.gateCommand)).getD tokens.size
  let mut findings : Array MessageData := #[]
  if index < gateIndex then
    if let some (_, text, position) := tokens[index]? then
      findings := findings.push
        m!"Whatwg axiom gate: the root WhatwgTest.lean contains a command other than imports and #whatwg_streams_axiom_gate: `{text}` at line {position.line}, column {position.column}"
  if gateIndex == tokens.size then
    findings := findings.push
      m!"Whatwg axiom gate: #whatwg_streams_axiom_gate is not the last command of the root: the root has no #whatwg_streams_axiom_gate command"
  else if let some (_, text, position) := tokens[gateIndex + 1]? then
    findings := findings.push
      m!"Whatwg axiom gate: #whatwg_streams_axiom_gate is not the last command of the root: `{text}` follows it at line {position.line}, column {position.column}"
  return findings

/-- Pass 0, the root pass (rule 4 of addendum V2c): the gate runs in the root;
the root's source, the text being elaborated, holds only imports, comments,
documentation and the gate command as its last command; and the root module has
declared no constant. -/
private def rootFindings (environment : Environment) (tokenTable : Parser.TokenTable)
    (projectRoot sourceFile : System.FilePath) (sourceText : String) : Array MessageData :=
  Id.run do
  let mut findings : Array MessageData := #[]
  let rootFile := projectRoot / "WhatwgTest.lean"
  if pathKey sourceFile != pathKey rootFile then
    findings := findings.push
      m!"Whatwg axiom gate: #whatwg_streams_axiom_gate runs in {sourceFile}, which is not the root {rootFile}; the gate runs only as the root's last command"
  let (tokens, failure?) := foldCodeTokens environment tokenTable sourceFile.toString sourceText
    (#[] : Array (RootTag × String × SourcePosition))
    fun tokens token position => tokens.push (rootTagOf token, tokenText token, position)
  if let some failure := failure? then
    findings := findings.push m!"{failure}"
  findings := findings ++ rootShapeFindings tokens
  let declared := (environment.constants.map₂.toList.map (·.1)).toArray.qsort
    fun left right => left.toString < right.toString
  for name in declared do
    findings := findings.push
      m!"Whatwg axiom gate: the root module WhatwgTest has declared a constant when the gate runs; the root must declare none, and it declares {name}"
  return findings

/-- Pass 1: every module source is imported by the test root, and (rule 5 of
addendum V2c) every environment module under an audited prefix maps, by exact
case-sensitive path, to exactly one scanned module source. -/
private def closureFindings (environment : Environment) (projectRoot sourceFile : System.FilePath)
    (sources : AuditedSources) : Array MessageData := Id.run do
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    pathKey (Lean.modToFilePath projectRoot moduleName "lean")
  let mut findings : Array MessageData := #[]
  for source in sources.modules do
    if pathKey source != pathKey sourceFile && !importedPaths.contains (pathKey source) then
      findings := findings.push
        m!"Whatwg module-closure gate: {source.toString} is not reachable from the WhatwgTest audit root"
  let scannedPaths := sources.modules.map pathKey
  for moduleName in environment.header.moduleNames do
    if (treeOf? moduleName).isNone then continue
    let path := pathKey (Lean.modToFilePath projectRoot moduleName "lean")
    let matching := (scannedPaths.filter (· == path)).size
    if matching == 0 then
      findings := findings.push
        m!"Whatwg module-closure gate: module {moduleName} is in the environment under an audited prefix but maps to no scanned source; its exact path would be {path}"
    else if matching != 1 then
      findings := findings.push
        m!"Whatwg module-closure gate: module {moduleName} is in the environment under an audited prefix and maps to {matching} scanned sources at {path}; exactly one is required"
  return findings

/-- Pass 2: tokenization failures and the `unsafe` and `partial` keywords. -/
private def modifierFindings (scans : Array SourceScan) : Array MessageData :=
  scans.flatMap fun scan =>
    let failures := match scan.failure? with
      | some failure => #[m!"{failure}"]
      | none => #[]
    failures ++ scan.modifiers.map fun hit =>
      m!"Whatwg source trust gate: {scan.source.toString} contains an authored `{hit.word}` declaration modifier at line {hit.line}, column {hit.column}"

/-- The pass after pass 2, token-table hygiene (rule 2 of addendum V2c): every
non-base token of the final table is inert. -/
private def tokenTableFindings (tokens : Array String) (nonBase : Array (String × Array Name)) :
    Array MessageData :=
  let splitters := tokens.filter fun token => token.any fun character => !isIdRest character
  nonBase.filterMap fun (token, declaredBy) =>
    let reasons := inertFailures splitters token
    if reasons.isEmpty then
      none
    else
      let declarers :=
        if declaredBy.isEmpty then "no module's parser entries; the module header adds it"
        else ", ".intercalate (declaredBy.toList.map toString)
      some m!"Whatwg source trust gate: token `{token}` of the final token table is not inert: {"; ".intercalate reasons.toList}; declared by {declarers}"

/-- Pass 3: what each audited constant is (contract section 4.1). -/
private def environmentFindings (environment : Environment)
    (declarations : Array AuditedDeclaration) : Array MessageData := Id.run do
  let mut findings : Array MessageData := #[]
  for declaration in declarations do
    let name := declaration.name
    if isGeneratedSafeRecursor environment name then continue
    let info ← match environment.find? name with
      | some info => pure info
      | none =>
          findings := findings.push
            m!"Whatwg trust gate: declaration {name} of module {declaration.moduleName} is missing from the environment"
          continue
    if info.isUnsafe then
      findings := findings.push m!"Whatwg trust gate: declaration {name} is unsafe"
    if info.isPartial then
      findings := findings.push m!"Whatwg trust gate: declaration {name} is partial"
    if let .axiomInfo _ := info then
      if isNativeAuxiliaryAxiom name then
        findings := findings.push
          m!"Whatwg trust gate: declaration {name} is a native-evaluation axiom (native_decide auxiliary)"
      else
        findings := findings.push
          m!"Whatwg trust gate: declaration {name} is an axiom; no audited tree declares one"
    if isExtern environment name then
      findings := findings.push
        m!"Whatwg trust gate: declaration {name} is `@[extern]`; host code replaces its checked body"
    if (Compiler.getImplementedBy? environment name).isSome then
      findings := findings.push
        m!"Whatwg trust gate: declaration {name} is `@[implemented_by]`; another declaration replaces its checked body in compiled code"
    if let .opaqueInfo opaqueInfo := info then
      if isSynthesizedOpaqueBody opaqueInfo.value then
        findings := findings.push
          m!"Whatwg trust gate: declaration {name} is an `opaque` with no authored body; Lean synthesised its value, so it denotes an inhabitant nobody chose"
  return findings

/-- The modules `metaprogrammingModules` lists. -/
private def listedMetaprogrammingModules : NameSet :=
  metaprogrammingModules.foldl (init := {}) fun listed entry => listed.insert entry.moduleName

/-- Pass 3, the environment half of rule 1 (addendum V2c.2): a registration is
attributed to the module whose entries record it and, when the registered
declaration belongs to another audited module, to that module as well; either
one that is not listed is refused. -/
private def registrationFindings (environment : Environment)
    (registrations : Array Registration) : Array MessageData := Id.run do
  let mut findings : Array MessageData := #[]
  for registration in registrations do
    unless listedMetaprogrammingModules.contains registration.moduleName do
      findings := findings.push
        m!"Whatwg trust gate: module {registration.moduleName} registers {registration.kind} but is not a listed metaprogramming module: {registration.detail}"
    if let some declaration := registration.declaration? then
      if let some owner := moduleOf? environment declaration then
        if owner != registration.moduleName && (treeOf? owner).isSome &&
            !listedMetaprogrammingModules.contains owner then
          findings := findings.push
            m!"Whatwg trust gate: module {owner} registers {registration.kind} but is not a listed metaprogramming module: {registration.detail}, whose declaration it owns, registered by module {registration.moduleName}"
  return findings

/-- The checks every strict-ceiling exception passes once it names a
declaration (contract section 6): its module is under a strict prefix, and it
reaches `Classical.choice`. -/
private def strictExceptionTargetFindings (environment : Environment) (declaration : Name) :
    CommandElabM (Array MessageData) := do
  if !environment.contains declaration then
    return #[m!"Whatwg axiom gate: strict-ceiling exception names missing declaration {declaration}"]
  let moduleName := (moduleOf? environment declaration).getD environment.mainModule
  if (strictPrefixOf? moduleName).isNone then
    return #[m!"Whatwg axiom gate: stale strict-ceiling exception for {declaration}; its module {moduleName} is under no strict prefix"]
  if !(← collectAxioms declaration).contains ``Classical.choice then
    return #[m!"Whatwg axiom gate: stale strict-ceiling exception for {declaration}; it does not reach Classical.choice"]
  return #[]

/-- Validate the strict prefixes and every strict-ceiling exception; return the
findings and the declarations the exceptions name. -/
private def strictCeilingFindings (environment : Environment)
    (declarations : Array AuditedDeclaration) :
    CommandElabM (Array MessageData × Array Name) := do
  let mut findings : Array MessageData := #[]
  for strictPrefix in strictCeilingPrefixes do
    if !(`Whatwg).isPrefixOf strictPrefix then
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling prefix {strictPrefix} is outside the Whatwg tree; ruling R-V1 keeps WhatwgTest and WhatwgGates under R-11" -- R-V3(c), 2026-10-01
    if !(declarations.any fun declaration => strictPrefix.isPrefixOf declaration.moduleName) then
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling prefix {strictPrefix} covers no audited module"
  let mut excepted : Array Name := #[]
  for entry in strictCeilingExceptions do
    if isBlank entry.reason then
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling exception for {entry.declaration} carries no reason"
    findings := findings ++ (← strictExceptionTargetFindings environment entry.declaration)
    excepted := excepted.push entry.declaration
  for entry in privateStrictCeilingExceptions do
    if isBlank entry.reason then
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling exception for {entry.original} (private to {entry.owner}) carries no reason"
    let owned := declarations.filter fun declaration =>
      declaration.moduleName == entry.owner &&
        privateToUserName? declaration.name == some entry.original
    match owned.toList with
    | [declaration] =>
        findings := findings ++ (← strictExceptionTargetFindings environment declaration.name)
        excepted := excepted.push declaration.name
    | [] =>
        findings := findings.push
          m!"Whatwg axiom gate: strict-ceiling exception names missing declaration {entry.original} (private to {entry.owner})"
    | _ =>
        findings := findings.push
          m!"Whatwg axiom gate: private strict-ceiling exception {entry.owner}/{entry.original} matched {owned.size} declarations; expected exactly one"
  let mut seen : NameSet := {}
  let mut repeated : NameSet := {}
  for name in excepted do
    if seen.contains name && !repeated.contains name then
      repeated := repeated.insert name
      findings := findings.push
        m!"Whatwg axiom gate: strict-ceiling exception for {name} is listed more than once"
    seen := seen.insert name
  return (findings, excepted)

/-- Pass 5: validate the exemption list, then refuse every refused token outside
an exempted source and every exemption whose source needs none (contract
sections 4.2 and 4.3). -/
private def trustTokenFindings (projectRoot : System.FilePath) (sources : AuditedSources)
    (scans : Array SourceScan) : Array MessageData := Id.run do
  let mut findings : Array MessageData := #[]
  let modulePaths := sources.modules.map (·.normalize)
  let entryPaths := sources.entryPoints.map (·.normalize)
  let mut exempted : Array (System.FilePath × Name) := #[]
  let mut listed : Array Name := #[]
  for exemption in sourceTokenExemptions do
    let moduleName := exemption.moduleName
    if isBlank exemption.reason then
      findings := findings.push
        m!"Whatwg source trust gate: source-token exemption for {moduleName} carries no reason"
    if listed.contains moduleName then
      findings := findings.push
        m!"Whatwg source trust gate: source-token exemption for {moduleName} is listed more than once"
      continue
    listed := listed.push moduleName
    let path := (Lean.modToFilePath projectRoot moduleName "lean").normalize
    let entryPath := (Lean.modToFilePath (projectRoot / "whatwgbin") moduleName "lean").normalize -- R-V3(c), 2026-10-01
    if entryPaths.contains path || entryPaths.contains entryPath then
      findings := findings.push
        m!"Whatwg source trust gate: source-token exemption for {moduleName} names an entry point under whatwgbin/, and no file under whatwgbin/ can be exempted" -- R-V3(c), 2026-10-01
    else if modulePaths.contains path then
      exempted := exempted.push (path, moduleName)
    else
      findings := findings.push
        m!"Whatwg source trust gate: source-token exemption names missing module {moduleName}"
  for scan in scans do
    match exempted.find? (·.1 == scan.source.normalize) with
    | some (_, moduleName) =>
        if scan.trustTokens.isEmpty then
          findings := findings.push
            m!"Whatwg source trust gate: stale source-token exemption for {moduleName}; its source contains no refused token"
    | none =>
        for hit in scan.trustTokens do
          findings := findings.push
            m!"Whatwg source trust gate: {scan.source.toString} contains an authored `{hit.word}` trust token at line {hit.line}, column {hit.column}"
  return findings

/-- Pass 5, the checks of `metaprogrammingModules` itself (addendum V2c.2):
an entry with a blank reason, one listed twice, one that names an entry point
under `whatwgbin/`, one that names no audited module source, and one whose
source spells no metaprogramming keyword while its module registers nothing. -/
private def metaprogrammingListFindings (environment : Environment)
    (projectRoot : System.FilePath) (sources : AuditedSources) (scans : Array SourceScan)
    (registrations : Array Registration) : Array MessageData := Id.run do
  let mut findings : Array MessageData := #[]
  let modulePaths := sources.modules.map pathKey
  let entryPaths := sources.entryPoints.map pathKey
  let mut listed : Array Name := #[]
  for entry in metaprogrammingModules do
    let moduleName := entry.moduleName
    if isBlank entry.reason then
      findings := findings.push
        m!"Whatwg trust gate: metaprogramming-module entry for {moduleName} carries no reason"
    if listed.contains moduleName then
      findings := findings.push
        m!"Whatwg trust gate: metaprogramming-module entry for {moduleName} is listed more than once"
      continue
    listed := listed.push moduleName
    let path := pathKey (Lean.modToFilePath projectRoot moduleName "lean")
    let entryPath := pathKey (Lean.modToFilePath (projectRoot / "whatwgbin") moduleName "lean")
    if entryPaths.contains path || entryPaths.contains entryPath then
      findings := findings.push
        m!"Whatwg trust gate: metaprogramming-module entry for {moduleName} names an entry point under whatwgbin/, which cannot be a metaprogramming module"
    else if !modulePaths.contains path then
      findings := findings.push
        m!"Whatwg trust gate: metaprogramming-module entry names missing module {moduleName}"
    else
      let spellsKeyword := scans.any fun scan =>
        pathKey scan.source == path && !scan.metaprogrammingKeywords.isEmpty
      let registers := registrations.any fun registration =>
        registration.moduleName == moduleName ||
          (registration.declaration?.bind (moduleOf? environment ·)) == some moduleName
      unless spellsKeyword || registers do
        findings := findings.push
          m!"Whatwg trust gate: stale metaprogramming-module entry for {moduleName}; its source declares no syntax, macro or elaborator and registers nothing"
  return findings

/-- Pass 5, the token half of rule 1 and rule 3 (addendum V2c.2 and V2c.4): a
metaprogramming keyword in code outside a listed module's source, and every
configuration site that fails the shape, in every audited source. -/
private def keywordAndShapeFindings (projectRoot : System.FilePath) (sources : AuditedSources)
    (scans : Array SourceScan) : Array MessageData := Id.run do
  let modulePaths := sources.modules.map pathKey
  let listedPaths := (metaprogrammingModules.map fun entry =>
    pathKey (Lean.modToFilePath projectRoot entry.moduleName "lean")).filter modulePaths.contains
  let mut findings : Array MessageData := #[]
  for scan in scans do
    unless listedPaths.contains (pathKey scan.source) do
      for hit in scan.metaprogrammingKeywords do
        findings := findings.push
          m!"Whatwg source trust gate: {scan.source.toString} contains an authored `{hit.word}` metaprogramming keyword at line {hit.line}, column {hit.column}"
  for scan in scans do
    for hit in scan.configShapes do
      findings := findings.push
        m!"Whatwg source trust gate: {scan.source.toString} contains a non-literal `config` option at line {hit.line}, column {hit.column}: {hit.word}"
  return findings

/-- Every pass, in order, over the project that holds `sourceFile`, the file the
gate command runs in, whose elaborated text is `sourceText`. Each pass logs every
finding; the summary line is logged only when no pass has one. -/
private def runGate (sourceFile : System.FilePath) (sourceText : String) : CommandElabM Unit := do
  let environment ← getEnv
  let some sourceDirectory := sourceFile.parent
    | throwError "Whatwg axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let sources ← liftIO <| auditedSources projectRoot
  let tokenTable := Parser.Module.updateTokens (Parser.getTokenTable environment)
  let mut clean := true

  -- 0. The root pass (addendum V2c, rule 4).
  clean := (← reportFindings
    (rootFindings environment tokenTable projectRoot sourceFile sourceText)) && clean

  -- 1. Module closure, in both directions (rule 5 is the reverse one).
  clean := (← reportFindings (closureFindings environment projectRoot sourceFile sources)) && clean

  -- 2. The modifier pass, over every audited source. The scan also records what
  -- pass 5 judges, so each source is tokenized once.
  let mut scans : Array SourceScan := #[]
  for source in sources.modules ++ sources.entryPoints do
    scans := scans.push (← liftIO <| scanSource environment tokenTable source)
  clean := (← reportFindings (modifierFindings scans)) && clean

  -- After pass 2, token-table hygiene (rule 2).
  let (tableTokens, nonBase) ← liftIO <| nonBaseTokens environment tokenTable
  clean := (← reportFindings (tokenTableFindings tableTokens nonBase)) && clean

  -- 3. The environment pass, over every constant of an audited module, then the
  -- environment half of rule 1 over every registration of one.
  let declarations ←
    match auditedDeclarations environment with
    | .ok found => pure found
    | .error message => throwError message
  let registrations := auditedRegistrations environment
  clean := (← reportFindings
    (environmentFindings environment declarations ++
      registrationFindings environment registrations)) && clean

  -- 4. The axiom pass: R-11 everywhere, the strict ceiling under its prefixes.
  let repositoryCeilingText := ceilingText ", " repositoryCeiling
  let strictCeilingText := ceilingText " and " strictCeiling
  let (exceptionFindings, excepted) ← strictCeilingFindings environment declarations
  let mut axiomFindings := exceptionFindings
  let mut choiceReachers : Array AuditedDeclaration := #[]
  for declaration in declarations do
    let name := declaration.name
    let axioms ← collectAxioms name
    for axiomName in axioms do
      if isNativeAuxiliaryAxiom axiomName then
        axiomFindings := axiomFindings.push
          m!"Whatwg axiom gate: declaration {name} reaches forbidden axiom {axiomName} (native_decide auxiliary)"
      else if forbiddenAxioms.contains axiomName then
        axiomFindings := axiomFindings.push
          m!"Whatwg axiom gate: declaration {name} reaches forbidden axiom {axiomName}"
      else if !repositoryCeiling.contains axiomName then
        axiomFindings := axiomFindings.push
          m!"Whatwg axiom gate: declaration {name} reaches unexpected axiom {axiomName}; the ceiling is {repositoryCeilingText}"
    if axioms.contains ``Classical.choice then
      choiceReachers := choiceReachers.push declaration
      if let some strictPrefix := strictPrefixOf? declaration.moduleName then
        if !excepted.contains name then
          axiomFindings := axiomFindings.push
            m!"Whatwg axiom gate: declaration {name} reaches Classical.choice under the strict ceiling of {strictPrefix}, which admits {strictCeilingText} only, and no exact exception names it"
  clean := (← reportFindings axiomFindings) && clean

  -- 5. The trust-token pass and its exemptions, then the token half of rule 1
  -- with the checks of its list, and rule 3.
  clean := (← reportFindings
    (trustTokenFindings projectRoot sources scans ++
      metaprogrammingListFindings environment projectRoot sources scans registrations ++
      keywordAndShapeFindings projectRoot sources scans)) && clean

  unless clean do
    return

  -- The summary: one line, counts only, in the template of contract section 7.
  let inTree (tree : Name) (found : Array AuditedDeclaration) : Nat :=
    (found.filter (·.tree == tree)).size
  let sourceCount := sources.modules.size + sources.entryPoints.size
  let whatwgReached := inTree `Whatwg choiceReachers
  let whatwgTotal := inTree `Whatwg declarations
  let testReached := inTree `WhatwgTest choiceReachers
  let testTotal := inTree `WhatwgTest declarations
  let gatesReached := inTree `WhatwgGates choiceReachers -- R-V3(c), 2026-10-01
  let gatesTotal := inTree `WhatwgGates declarations -- R-V3(c), 2026-10-01
  let prefixCount := strictCeilingPrefixes.length
  let exceptionCount :=
    strictCeilingExceptions.length + privateStrictCeilingExceptions.length
  let exemptionCount := sourceTokenExemptions.length
  logInfo m!"Whatwg module and axiom gate: checked {sourceCount} source files and {declarations.size} declarations; Classical.choice is reached by {whatwgReached} of {whatwgTotal} declarations in Whatwg, {testReached} of {testTotal} in WhatwgTest and {gatesReached} of {gatesTotal} in WhatwgGates; strict ceiling propext and Quot.sound over {prefixCount} module prefix(es) with {exceptionCount} exact exception(s); {exemptionCount} source-token exemption(s)" -- R-V3(c), 2026-10-01

/-! ## The gate command and the post-command check -/

/-- The gate command, run as the last command of the root `WhatwgTest.lean`. -/
syntax "#whatwg_streams_axiom_gate" : command

/-- The syntax kind of the gate command. -/
private def gateKind : Name :=
  ``«command#whatwg_streams_axiom_gate»

/-- The gate's own elaborator: every pass, over the file the command runs in. -/
@[command_elab «command#whatwg_streams_axiom_gate»]
private def elabAxiomGate : CommandElab := fun _ => do
  let sourceFile ← liftIO <| absoluteSourcePath (System.FilePath.mk (← getFileName))
  runGate sourceFile (← getFileMap).source

/-- The file being elaborated, when it is the root: `WhatwgTest.lean` in the
directory that holds `Whatwg.lean`, compared exactly. Every other module that
imports this one, a plant included, is not the root, so the post-command check
does nothing there. -/
private def rootFile? : CommandElabM (Option System.FilePath) := do
  let sourceFile ← liftIO <| absoluteSourcePath (System.FilePath.mk (← getFileName))
  unless sourceFile.fileName == some "WhatwgTest.lean" do
    return none
  let some sourceDirectory := sourceFile.parent | return none
  try
    let projectRoot ← liftIO <| findProjectRoot sourceDirectory
    if pathKey (projectRoot / "WhatwgTest.lean") == pathKey sourceFile then
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
    match moduleOf? environment declaration with
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
