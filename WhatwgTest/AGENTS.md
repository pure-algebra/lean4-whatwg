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

Axiom reports cover every exported theorem named by a graph trust edge or leaf
receipt set and record the actual dependencies. Conformance tests name both
observations being compared, the observation mask, and any loss admitted by
the bridge. Creating a test does not by itself force a proof graph: passive
finite alphabets and value records remain on the leaf-receipt route unless
they acquire a semantic or cutover-bearing claim.

## Spec coverage witnesses

`WhatwgTest/Audit/SpecCoverage.lean`, once P1 lands it, is the
numerator of the specification coverage metric: one frozen row per census
algorithm, its disposition, coverage state, witnesses with axiom receipts, and
every witness statement frozen by `#check (@name : proposition)` ascription. A
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
`bin/Census.lean` hands all three to `Gates.Census.cli` keyed by standard;
Infra has no numerator and therefore no report.

## Audit implementation

`WhatwgTest/Audit/AxiomGate.lean` admits no module by name to a wider
ceiling: the implementation ceiling and its audit-module list are gone (ruling
R-V1). R-11's ceiling binds every audited tree, this one and the gate itself
included, so an audit module that reaches `Classical.choice` through `MetaM`
needs no entry. The one narrower bound is the strict ceiling, `propext` and
`Quot.sound` only, over the production modules under the gate's
`strictCeilingPrefixes`; a declaration there that reaches `Classical.choice`
is admitted only by an exact entry of `strictCeilingExceptions` (or
`privateStrictCeilingExceptions`, by owning module and original name) with its
reason, and an entry that names no declaration, sits under no strict prefix,
no longer reaches `Classical.choice`, or carries no reason fails the build.

The gate's token pass (ruling R-V2) refuses, in code, the trust words no
constant records, in every source of this tree, `Whatwg/`, `Gates/` and `bin/`.
A module that must spell one in code is admitted to that pass, and to no other
check, by an exact entry of `sourceTokenExemptions`; an entry whose module has
no source, or whose source carries no refused word, fails the build, and no
file under `bin/` can be exempted. The list is empty: the gate spells its own
words as string and name literals. `test/contracts/trust-gate-hardening.contract.md`
freezes this behaviour and `lake exe trustselftest` plants its violations.

Before handoff, run the narrow file directly and the default Lake build. Link
the exact command and result to the affected proof-graph edge or leaf receipt;
do not mark the whole type closed from one green test.
