import WhatwgGates.Trust.Registrations
import WhatwgGates.Trust.Root
import WhatwgGates.Trust.TokenTable

/-!
# Gates.Trust.Gate

The trust gate's run: every pass of the gate library, in the order of section 3
of `test/contracts/trust-gate-hardening.contract.md` as addendum V2c.1 extends
it, over one repository's `Config`, and the summary of section 7. Both judges of
the tree call it (ruling R-W7(a), addendum V2e): the in-tree command
`#whatwg_streams_axiom_gate` of `WhatwgTest/Audit/AxiomGate.lean`, and the
executable gate over built `.olean` files.

## Passes, in order

Every pass runs and hands every finding it has to the host, in this order; the
summary is returned only when no pass has a finding. The contract's section 3
admits a gate that collects every finding, and this one must: six older plants
(V2-T03, V2-T04, V2-T08, V2-T09, V2-T10 and V2b-T10) declare a `macro` or an
`elab` in a module that is not a metaprogramming module, so rule 1 refuses each
at the environment pass, and a gate that stopped there would never print the
trust-token fragment each of those rows expects. The order still decides which
message comes first.

0. *Root pass* (V2c rule 4, before step 1, `WhatwgGates/Trust/Root.lean`). The
   root holds only `import` lines, comments, documentation and
   `#whatwg_streams_axiom_gate`, which is its last command, and the root module
   has declared no constant when the gate runs. The gate runs only in the root.
1. *Module closure* (`WhatwgGates/Trust/Sources.lean`). Every module source is
   imported by the test root, and (V2c rule 5) every environment module under an
   audited prefix maps, by exact case-sensitive path, to exactly one scanned
   source. A file whose extension is `lean` in any case is scanned, so a `.LEAN`
   file that a case-insensitive host builds is reported in both directions,
   never skipped. `whatwgbin/` is excluded: its files are executable roots no
   audit root imports.
2. *Modifier pass* (`WhatwgGates/Trust/Tokens.lean`). An authored `unsafe` or
   `partial` keyword in code, in any audited source, `whatwgbin/` included, is
   refused; so is a source the tokenizer cannot read to its end. After it, as a
   pass of its own, *token-table hygiene* (V2c rule 2,
   `WhatwgGates/Trust/TokenTable.lean`): every token of the final table, scoped
   entries included, that neither the `lean` binary nor an `Init` module
   declares must be inert (tests T1 to T3 of addendum V2c.3), so that no token
   hides a refused word from the source passes, whoever declared it.
3. *Environment pass* (`WhatwgGates/Trust/Environment.lean`). Over every
   constant of an audited module, apart from a generated safe recursor: an
   `unsafe` or `partial` constant, a declared axiom (a native-evaluation
   auxiliary named as such), an `@[extern]` or `@[implemented_by]` constant,
   and an `opaque` whose value Lean synthesised. Then (V2c rule 1, environment
   half, `WhatwgGates/Trust/Registrations.lean`) every registration an audited
   module's entries record: a token, parser, syntax category, macro, elaborator
   or initializer, refused unless both the recording module and, when it is
   audited, the module that owns the registered declaration are listed in
   `metaprogrammingModules`.
4. *Axiom pass* (`WhatwgGates/Trust/Axioms.lean`). The axioms each constant
   reaches, as the host's `axiomsOf` gives them. `sorryAx`, `Lean.ofReduceBool`,
   `Lean.ofReduceNat`, `Lean.trustCompiler` and every native-evaluation
   auxiliary are forbidden everywhere. Ruling R-11's ceiling, `propext`,
   `Quot.sound` and `Classical.choice`, binds every audited tree. Ruling R-V1's
   strict ceiling, `propext` and `Quot.sound` only, binds every constant whose
   module is under a prefix of `strictCeilingPrefixes`, unless an exact entry of
   `strictCeilingExceptions` or `privateStrictCeilingExceptions` names it; every
   entry is checked for need.
5. *Trust-token pass* (`WhatwgGates/Trust/Tokens.lean`). A token of code that
   carries a word of `refusedWords`, in any audited source, is refused unless
   the source's module has an exact entry in `sourceTokenExemptions`; every
   entry is checked for need. Then (V2c rule 1, token half) a metaprogramming
   keyword in code outside a listed module, the five checks of
   `metaprogrammingModules` itself, and (V2c rule 3,
   `WhatwgGates/Trust/ConfigShape.lean`) every `(config := …)` whose value is
   not a literal brace group without `with` closed by `)`.

A successful run reports one summary line with the per-tree counts of
declarations that reach `Classical.choice` (`WhatwgGates/Trust/Report.lean`);
addendum V2c adds no field.

## What the host supplies

The passes read the configuration, the environment the host hands in, the
audited sources on disk and the host's reads, and nothing of an elaboration
context. The host supplies, as `HostReads`, the final token table, every scoped
`.token` entry and the constants the root module has declared, and, as `Host`,
the axioms of one constant and the printing of one pass's findings. Every other
read of an extension is `getModuleEntries` or `getModuleIREntries`, which an
import fills in whether or not it loads the extensions, so a host that imports
with `loadExts := false` can run every pass.

The audited sources are a third input. `runPasses` reads them from disk.
`runPassesOver` takes the project root, the source list and a scan function, and
holds every pass and their order; `runPasses` calls it. The trust self-test calls
it with a planted source list and a scan that answers a planted text from memory
(addendum V2g of the contract), so a plant is judged by the run both hosts make.

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
and `Foo.native` are names, and `«sorry»` is refused like `sorry`. The library
spells every refused word and every metaprogramming keyword as a string literal
and every axiom as a name literal, so it needs no exemption; it declares no
syntax and runs nothing at elaboration, so it is no metaprogramming module.

`Parser.testParseFile` cannot replay an already-compiled source against the
final project environment: syntax introduced by a later-imported test module
can turn an earlier ordinary identifier into a keyword. Tokenization is the
right level for the source passes, and token-table hygiene bounds what a later
module's syntax can do to that tokenization; the environment pass independently
confirms what the compiled constants and registrations are.

Sections 13, V2b.6, V2c.7 and V2e.7 of the contract state what a green gate
does not mean: among others, a name built by metaprogramming, an option set
outside the source, a dependency's syntax and macros, and the toolchain's own
non-inert base tokens are invisible to these passes, and `whatwgbin/` is read by
the source passes only.

This gate began as a port of lean4-effect4's `Effect4Test/Audit/AxiomGate.lean`;
the environment pass follows that gate at `0f16828a`, as R-V2 directs.
-/

namespace Gates.Trust

open Lean

/-- What only the gate's host can read, handed to the passes as data: the
in-tree command reads each from its elaboration state, and an executable over
built files reads its equivalent from their raw entries. -/
structure HostReads where
  /-- The final token table every source pass tokenizes with. -/
  tokenTable : Parser.TokenTable
  /-- Every scoped `.token` entry of the environment, which token-table hygiene
  adds to the final table (addendum V2c.3). -/
  scopedTokens : Array String
  /-- The constants the root module has declared when the gate runs; none for a
  host that does not elaborate the root. -/
  rootConstants : Array Name

/-- What the gate's host does for the passes. -/
structure Host (m : Type → Type) where
  /-- The axioms one constant reaches. -/
  axiomsOf : Name → m (Array Name)
  /-- Print every finding of one pass, in order; called once per pass, also when
  the pass has none. -/
  report : Array String → m Unit

/-- Hand every finding of one pass to the host, and say whether there was none. -/
def reportFindings {m : Type → Type} [Monad m] (host : Host m)
    (findings : Array String) : ExceptT String m Bool := do
  host.report findings
  return findings.isEmpty

/-- Every pass, in order, over the audited `sources` of the project at
`projectRoot`, each read through `scan`, for the file the gate runs for,
`sourceFile`, whose text is `sourceText` (contract section 3, as addendum V2c.1
extends it). Each pass hands its findings to `host.report`; the summary is
returned only when no pass has a finding. The error is a failure that stops the
run: an environment whose module tables disagree.

`runPasses` calls it with the sources on disk. The trust self-test calls it with
a planted source list and a `scan` that answers a planted text from memory
(addendum V2g), so that a plant is judged by this run and not by a copy of it. -/
def runPassesOver {m : Type → Type} [Monad m] [MonadLiftT IO m] (config : Config)
    (host : Host m) (environment : Environment) (reads : HostReads)
    (projectRoot : System.FilePath) (sources : AuditedSources)
    (scan : System.FilePath → m SourceScan)
    (sourceFile : System.FilePath) (sourceText : String) :
    ExceptT String m (Option Summary) := do
  let tokenTable := reads.tokenTable
  let mut clean := true

  -- 0. The root pass (addendum V2c, rule 4).
  clean := (← reportFindings host
    (rootFindings environment tokenTable projectRoot sourceFile sourceText
      reads.rootConstants)) && clean

  -- 1. Module closure, in both directions (rule 5 is the reverse one).
  clean := (← reportFindings host
    (closureFindings config environment projectRoot sourceFile sources)) && clean

  -- 2. The modifier pass, over every audited source. The scan also records what
  -- pass 5 judges, so each source is tokenized once.
  let mut scans : Array SourceScan := #[]
  for source in sources.modules ++ sources.entryPoints do
    scans := scans.push (← (scan source : m _))
  clean := (← reportFindings host (modifierFindings scans)) && clean

  -- After pass 2, token-table hygiene (rule 2).
  let (tableTokens, nonBase) ← nonBaseTokens environment tokenTable reads.scopedTokens
  clean := (← reportFindings host (tokenTableFindings tableTokens nonBase)) && clean

  -- 3. The environment pass, over every constant of an audited module, then the
  -- environment half of rule 1 over every registration of one.
  let declarations ←
    match auditedDeclarations config environment with
    | .ok found => pure found
    | .error message => throwThe String message
  let registrations := auditedRegistrations config environment
  clean := (← reportFindings host
    (environmentFindings environment declarations ++
      registrationFindings config environment registrations)) && clean

  -- 4. The axiom pass: R-11 everywhere, the strict ceiling under its prefixes.
  let (axiomFindings, choiceReachers) ←
    (axiomPassFindings config host.axiomsOf environment declarations : m _)
  clean := (← reportFindings host axiomFindings) && clean

  -- 5. The trust-token pass and its exemptions, then the token half of rule 1
  -- with the checks of its list, and rule 3.
  clean := (← reportFindings host
    (trustTokenFindings config projectRoot sources scans ++
      metaprogrammingListFindings config environment projectRoot sources scans registrations ++
      keywordAndShapeFindings config projectRoot sources scans)) && clean

  unless clean do
    return none

  -- The summary: counts only, in the template of contract section 7.
  let inTree (tree : Name) (found : Array AuditedDeclaration) : Nat :=
    (found.filter (·.tree == tree)).size
  return some
    { sourceCount := sources.modules.size + sources.entryPoints.size
      declarationCount := declarations.size
      whatwgReached := inTree `Whatwg choiceReachers
      whatwgTotal := inTree `Whatwg declarations
      testReached := inTree `WhatwgTest choiceReachers
      testTotal := inTree `WhatwgTest declarations
      gatesReached := inTree `WhatwgGates choiceReachers -- R-V3(c), 2026-10-01
      gatesTotal := inTree `WhatwgGates declarations -- R-V3(c), 2026-10-01
      prefixCount := config.strictCeilingPrefixes.length
      exceptionCount :=
        config.strictCeilingExceptions.length + config.privateStrictCeilingExceptions.length
      exemptionCount := config.sourceTokenExemptions.length }

/-- Every pass, in order, over the project that holds `sourceFile`, the file the
gate runs for, whose text is `sourceText`: `runPassesOver` with the audited
sources read from disk. The error is a failure that stops the run: a source file
with no parent directory, or an environment whose module tables disagree. -/
def runPasses {m : Type → Type} [Monad m] [MonadLiftT IO m] (config : Config)
    (host : Host m) (environment : Environment) (reads : HostReads)
    (sourceFile : System.FilePath) (sourceText : String) :
    ExceptT String m (Option Summary) := do
  let some sourceDirectory := sourceFile.parent
    | throwThe String "Whatwg axiom gate: source file has no parent directory"
  let projectRoot ← findProjectRoot sourceDirectory
  let sources ← auditedSources projectRoot
  runPassesOver config host environment reads projectRoot sources
    (fun source => monadLift (scanSource environment reads.tokenTable source))
    sourceFile sourceText

end Gates.Trust
