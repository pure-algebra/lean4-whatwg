# Whatwg Lean-test routing

This boundary contains executable Lean attacks, examples, conformance
checks, and proof receipts. The repository root rules remain in force;
`docs/AGENT-ROUTING.md` defines the shared type-assurance and counterexample
route.

## Breaker ownership

A breaker freezes a contract and its red battery before the corresponding
implementation. A builder may repair test elaboration without changing the
attacked statement, witness, or acceptance condition, but does not weaken or
delete a breaker-owned test.

Every counterexample that can alter a declaration or cutover decision receives
a stable ID in `test/counterexamples/REGISTER.md`. Put the executable Lean
witness under `WhatwgTest/Streams/Counterexamples/<Area>/` and link it from
the registry and owning contract. Keep the witness after the implementation
rejects it so the repair remains testable.

A frozen red battery is declared in `test/fixtures/trust-gate/known-red.txt`
for the duration of its red phase, and removed the moment the builder turns it
green. The trust self-test checks that declaration in both directions.

## Evidence classes

Tests distinguish theorem evidence, finite executable probes, model checks,
and host observations. A passing example does not become a general law. A
compile-time rejection records the exact rejected declaration or term rather
than relying on an error-message substring unless the diagnostic text itself
is the contract.

A battery freezes a statement with `#whatwg_freeze (@name : proposition)`
(`WhatwgTest/Audit/Freeze.lean`, `test/contracts/freeze-registry.contract.md`,
ruling R-W5). The command elaborates the proposition alone, refuses a hole,
requires it to be the declared statement with nothing unfolded but `let`,
`have` and auxiliary matchers, and for a theorem requires the exact axiom set
in its `axioms [..]` clause; it prints nothing and adds one checked entry,
`<module>.frozen.<name>`. That clause is the theorem's axiom receipt: the
separate `*AxiomReport.lean` modules were retired by the conversion (ruling
R-W27). A battery docstring, contract or receipts log written before it that
says `#check (@name : proposition)` or names a report module is left as
written and read with this paragraph. The witness receipts of the
counterexample modules still print with `#print axioms`. A new battery is
written with `#whatwg_freeze` from its freeze, with a `mask` clause for each
theorem that has an observation mask. Conformance tests name both
observations being compared, the observation mask, and any loss admitted by
the bridge. Creating a test does not by itself force a proof graph: passive
finite alphabets and value records remain on the leaf-receipt route unless
they acquire a semantic or cutover-bearing claim.

## Spec coverage witnesses

`WhatwgTest/Audit/SpecCoverage.lean`, once P1 lands it, is the
numerator of the specification coverage metric: one frozen row per census
algorithm, its disposition, coverage state, witnesses with axiom receipts, and
every witness statement frozen by a `#whatwg_freeze (@name : proposition)`
entry. A
witness is a `theorem` whose receipt stays inside the ceiling (`propext`,
`Quot.sound`, `Classical.choice`, ruling R-11); a row is `green` only when
every step of its algorithm is a named theorem or an assertion discharged by
typing.
`docs/SPEC-COVERAGE.md` owns the rules.

Slice Q2 of `docs/PROMISE-PACKAGE-PLAN.md` added two more numerators,
`WhatwgTest/Audit/WebIdl/SpecCoverage.lean` and
`WhatwgTest/Audit/Ecma262/SpecCoverage.lean`, one per promise-lane standard.
Both are thin at Q2: `emit` is the generated all-`absent` scaffold, no row
carries a witness, and the module's freeze is the pair of expected totals,
checked at elaboration. They declare no theorem and read no file, and like
every module of this tree they stay under R-11's ceiling (below).
`whatwgbin/Census.lean` hands all three to `Gates.Census.cli` keyed by standard;
Infra has no numerator and therefore no report.

## Audit implementation

The trust gate is the command `#whatwg_streams_axiom_gate` of
`WhatwgTest/Audit/AxiomGate.lean`, which the test root runs last. Since the
factor of addendum V2e.3 (ruling R-W7(a)) that module is a thin wrapper: the
command, the reads only an elaborating process can make, and the post-command
linters. Every pass lives in the gate library `WhatwgGates/Trust/*.lean`
(`Gates.Trust.runPasses`), which takes the configuration as an argument, and
this repository's data, the audited trees, the two ceilings, the strict
prefixes and the three exact lists below, lives in
`WhatwgGates/TrustConfig.lean` (`Gates.TrustConfig.config`), each list below its
frozen anchor comment. A list entry is therefore added there, and a change to a
pass is a change to the library.

The same passes run a second time, outside the tree they audit, in the
executable gate `lake exe whatwg_trustgate` (addendum V2e.5): after `lake
build`, it reads the built `.olean` files with no extension loaded, so no audited
initializer, macro or elaborator runs in its process and none can replace or
silence it (debt D56); it refuses a missing or stale `.olean`, so its verdict is
never a cached replay (debt D61), a module compiled with `warningAsError` off, a
`debug.*` or `warn.sorry` option or a non-`-D` argument, a `weakLeanArgs` in
`lakefile.toml`, and an audited entry in an environment extension that the
fourth list, `extensionAllowlist`, does not name with its reason. It judges this
root lexically and never imports it, so it does not read the root's own
constants; the in-tree command still does. On the unmodified tree it prints the
in-tree summary line after `PASS whatwg_trustgate: `. The in-tree command stays
for this lane (ruling R-W7(a)); addendum V2e.7 makes the executable, run after
`lake build`, the deciding trust check in CI.

The gate admits no module by name to a wider ceiling: the implementation
ceiling and its audit-module list are gone (ruling R-V1). R-11's ceiling binds every audited tree, this one and the gate itself
included, so an audit module that reaches `Classical.choice` through `MetaM`
needs no entry. The one narrower bound is the strict ceiling, `propext` and
`Quot.sound` only, over the production modules under the configuration's
`strictCeilingPrefixes`; a declaration there that reaches `Classical.choice`
is admitted only by an exact entry of `strictCeilingExceptions` (or
`privateStrictCeilingExceptions`, by owning module and original name) with its
reason, and an entry that names no declaration, sits under no strict prefix,
no longer reaches `Classical.choice`, or carries no reason fails the build.

The gate's token pass (ruling R-V2) refuses, in code, the trust words no
constant records, in every source of this tree, `Whatwg/`, `WhatwgGates/` and `whatwgbin/`.
A module that must spell one in code is admitted to that pass, and to no other
check, by an exact entry of `sourceTokenExemptions`; an entry whose module has
no source, or whose source carries no refused word, fails the build, and no
file under `whatwgbin/` can be exempted. The list is empty: the gate spells its own
words as string and name literals.

The third list, `metaprogrammingModules` (addendum V2c, ruling R-V10), names the
modules that may declare syntax, a macro or an elaborator, or run a metaprogram
at elaboration (`run_cmd`, `#eval`, `initialize` and the rest of the keyword set
of V2c.2). Outside it the token pass refuses those keywords in code, and the
environment pass refuses an audited module that registers a token, parser,
syntax category, macro, elaborator or initializer, whatever spelled it, such as
an `@[command_elab]` attribute. A listed module stays bound by every trust
word: the list relaxes rule 1 and nothing else. It holds the nine modules that
declare a `#…` command, the gate's own module and the freeze registry's
included, and the two constructive-contract batteries that run their receipts in `run_cmd`, each with
its reason; an entry that names no audited module source, one whose module
neither spells a keyword nor registers anything, one with a blank reason, one
listed twice, and one that names an entry point under `whatwgbin/` fail the
build. A new elaboration-time battery that needs `elab` or `run_cmd` therefore
needs an entry, reviewed like an exemption.

The same addendum makes the gate refuse a token of the final token table that
is not inert (one that could hide a refused word from the token pass), a
`(config := …)` whose value is not a literal brace group without `with` closed
by `)`, any command of `WhatwgTest.lean` other than its imports and the gate
command, which must come last, a constant that root declares, and an audited
environment module that maps to no scanned source by exact path. Because the
gate is a command inside the tree it audits, its module also registers linters
that check, after the root's commands, that the gate's own elaborator ran it,
and run every pass themselves when it did not.
`test/contracts/trust-gate-hardening.contract.md` freezes this behaviour and
`lake exe whatwg_trustselftest` plants its violations.

Before handoff, run the narrow file directly and the default Lake build. Link
the exact command and result to the affected proof-graph edge or leaf receipt;
do not mark the whole type closed from one green test.
