# lean4-WHATWG-streams — agent operating rules

This file is the always-loaded router for work in this repository. Read it in
full, then open only the authority documents named for the current task.

## Authority map

| Path | Owns |
| --- | --- |
| `COORDINATION.md` | live claims between concurrent agents, and what past collisions cost |
| `PLAN.md` | phases, entry and exit gates, current phase, research holds |
| `SPEC-MANIFEST.md` | authority pins, authority order, section dispositions of the specification |
| `docs/ARCHITECTURE.md` | module boundaries, dependency direction, public API policy |
| `docs/DESIGN-BASIS.md` | adopted architecture decisions and the role of each primary source |
| `docs/AGENT-ROUTING.md` | the router hierarchy, declaration records, and the assurance threshold |
| `docs/SPEC-COVERAGE.md` | definition, vocabulary, and the one report format of specification coverage |
| `docs/PROVENANCE.md` | every pin: digest, fetch command, cross-check, license |
| `docs/SHA256-DAG.md` | pointer: the SHA-256 proof graph lives in lean4-hash, which the gates require |
| `test/contracts/` | breaker-authored contracts and executable falsifiers |
| `test/counterexamples/` | central counterexample register and durable witnesses |
| `Whatwg/Streams/` | library declarations and proofs |
| `WhatwgTest/Streams/` | Lean tests, attacks, receipts, and the axiom gate |
| `WhatwgGates/` | repository gates implemented in Lean |
| `WhatwgTest/Ledger/` | the graph ledger: the ten edges of every proof graph, with their status, grounds and open items, as checked Lean data (ruling R-W6); `generated/graphs/` is its projection |
| `harness/` | host conformance evidence |
| `generated/` | deterministic projections only; never hand-edited |
| `vendor/` | sealed pinned third-party bytes; never edited |

If two files appear to own the same fact, stop and repair the ownership map.

More than one agent may edit this worktree at once. Direct messaging is not a
durable ownership record, so every agent reads `COORDINATION.md` before
writing and records a file claim there before freezing a packet or changing a
shared surface.

## Development order

1. Freeze the public declaration record, existing-type disposition with its
   specification anchor, and assurance route.
2. A breaker, in a separate process, commits the contract and red battery, and
   declares the red modules in `test/fixtures/trust-gate/known-red.txt`.
3. The builder implements without editing that packet or battery, and removes
   the known-red entries when the battery turns green.
4. Run the narrow test, `lake build`, the axiom receipt, and the gates under
   "Gates" below that apply to every change.
5. An independent reviewer checks model intent, proof trust, spec fidelity,
   and claim scope.
6. Close the required assurance route: a proof graph for semantic or
   cutover-bearing work, or local signature and theorem receipts for a trivial
   finite leaf. No category or cutover may hide an open graph edge or leaf
   receipt.

Every exported declaration receives a lightweight ownership, disposition, and
duplicate-prevention record. A proof graph is mandatory for admission or
refusal, judgments or denotations, interpreters, state-machine transition
laws, reification or generated-code relations, nontrivial composition or
recursive invariants, external semantic equivalence, and declarations that
directly gate cutover. Empty stubs have no declaration to record and need no
graph. `docs/AGENT-ROUTING.md` owns the full threshold.

Breadth precedes depth: every major category receives a frozen representative
contract before one category is developed far beyond the others.

## Authority order

1. The specification source `index.bs` at the pinned commit is the semantic
   owner. A theorem models a named algorithm, internal slot, IDL member, or
   requirement of that text, anchored by span digest.
2. The specification's reference implementation at the same commit is
   second-tier evidence: one candidate realizer where the text states
   requirements, and a reading aid where the text states algorithms. It never
   repairs a theorem statement.
3. Web Platform Tests at the pinned commit are the host conformance corpus.
4. Node, Bun, and the reference implementation under Node are local host
   profiles. Browser engines enter only through published WPT results cited
   by run identifier.

A host that disagrees with the specification produces a host-profile refusal
row, never a change to the model.

## Representation rules

- Canonical program and stream content is first-order data. Lean functions,
  host closures, promises, and runtime objects are not stored content.
- Underlying source, sink, and transformer algorithms supplied by user code
  are foreign boundaries with profiles: their answers are typed decisions on
  the tape, never modelled bodies.
- Full meaning is relational over explicit decisions. The decision kinds are
  consumer calls, foreign-boundary answers and their settlement timing, and
  abort signals. Promise-job order is deterministic state, not a decision.
- Every theorem names its observation mask. The two pre-registered masks are
  M1, chunk sequence plus terminal outcome, and M2, full settlement order.
- Fuel exhaustion and unanswered decisions are live frontiers, never errors
  or refusals.
- Fixed-fuel execution is not assigned a general bind law. Composition is
  proved at the big-step face.
- Readable, writable, transform, piping, queuing strategies, and
  queue-with-sizes are distinct calculi or layers with explicit embeddings;
  type mention alone does not make a primitive.
- Byte streams and BYOB are a later calculus (P9); ArrayBuffer detachment is a
  foreign boundary. Transferable streams are refused with a refusal theorem,
  never modelled.
- TypeScript is one target profile, not the identity or semantic owner.

## Counterexamples and claims

All counterexamples that can change a declaration or cutover decision have a
stable ID in `test/counterexamples/REGISTER.md`. Proof sources remain beside
the attacked code and are linked, not copied into prose.

Do not say "sound", "equivalent", "preserves", "conforms", "fully reified",
or "complete" without naming the exact judgment, observation mask, theorem or
gate, assumptions, and remaining host boundary. A compiling finite probe is
reported as a finite probe. A passing WPT case is reported as a host
observation under a named profile.

Coverage of the specification is stated only in the block printed by the
coverage report defined in `docs/SPEC-COVERAGE.md`, pasted verbatim with its
commit. No percentage is computed by hand.

## Gates

Every gate is Lean and runs under the pinned toolchain. Shell files only
orchestrate; they decide nothing.

| Command | Decides |
| --- | --- |
| `lake build` | the libraries elaborate; the elaboration-time axiom gate in `WhatwgTest.lean` passes over every declaration |
| `lake exe whatwg_vendorseal` | `vendor/` and `generated/vendor-manifest.tsv` agree in both directions; every path is valid on Windows |
| `lake exe whatwg_citations` | no line-numbered citation into a protected authored document |
| `lake exe whatwg_ledger` | every reference of the graph ledger resolves against the built modules and the authored files; a ruling of `COORDINATION.md` that names a graph is cited or acknowledged by that graph; a register row's status agrees with the cells that cite it; every module under `Whatwg` that declares a constant has exactly one owner, a graph's fence, a leaf record or an unrouted prefix that cites a debt (ruling R-W22); `generated/graphs/`, with its `INDEX.md`, is byte-identical to a fresh rendering |
| `lake exe whatwg_declsnapshot` | `generated/declarations/` is byte-identical to a fresh snapshot of the built production libraries, and declaration records, freeze entries and census rows join under the rules of `test/contracts/declaration-snapshot.contract.md` |
| `lake exe whatwg_trustgate` | run after `lake build`: every audited module has a built `.olean` that matches its source, its trace and the options `lakefile.toml` fixes; every pass of the in-tree gate holds over the built modules, read with no extension loaded and no audited code run; every environment extension an audited module writes to is on the exact allowlist of `WhatwgGates/TrustConfig.lean`; the executable links no audited metaprogramming module (ruling R-W7, addendum V2e of `test/contracts/trust-gate-hardening.contract.md`) |
| `lake exe whatwg_trustselftest` | every planted trust-gate violation is refused for its frozen reason, every control is accepted, and the gate runs by relative file name |
| `lake env leanchecker Whatwg WhatwgTest WhatwgGates` | every declaration of every built module under those three prefixes replays in the kernel |

Every row applies to every change except two (ruling R-W25). The trust
self-test tests the gate's own code: run it when a change touches that code
(`WhatwgGates/Trust/`, `WhatwgTest/Audit/AxiomGate.lean`, the self-test and
the two entry points), its configuration `WhatwgGates/TrustConfig.lean`, its
fixtures under `test/fixtures/trust-gate/` other than `known-red.txt`,
`lakefile.toml` or a pin; the coordinator also runs it once at a lane's
close. A slice that touches none of these does not run it. A seat runs
`leanchecker` over the module prefixes it added or changed, and the
coordinator runs it over the three trees at each merge.

The axiom ceiling is Lean's standard base, `propext`, `Quot.sound`, and
`Classical.choice`, for every tree (operator ruling R-11, 2026-09-02;
`Classical.choice` enters through library proofs about `String` and
`Vector` and never through computation, and forbidding it bought re-proved
lemmas, not soundness). A stricter ceiling, `propext` and `Quot.sound` only,
binds every declaration whose module is under a prefix of the strict list in
`WhatwgGates/TrustConfig.lean` (rulings R-V1 and R-W19): `Whatwg.Ecma262`,
`Whatwg.WebIdl`, `Whatwg.Url`, `Whatwg.Infra.Text.Utf8` and `Whatwg.Streams`
since the lane V landing, and `Whatwg.Signatures` since the Q5 landing
(rulings R-W3 and R-W16). A declaration there that reaches `Classical.choice` is
admitted only by an exact exception beside the list, with its reason, and an
exception that has outlived its reason fails the build. `sorryAx`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, and the
`native_decide` auxiliary axioms are forbidden everywhere. The gate also
refuses, in every audited tree, a declared `axiom`, an `@[extern]` or
`@[implemented_by]` declaration and an `opaque` whose body Lean synthesised.
In code under `Whatwg/`, `WhatwgTest/`, `WhatwgGates/` and `whatwgbin/`,
inside an `example` included, it refuses every token that opens a trust
channel no constant records (rulings R-V2 and R-V6; the word list is section
4.2 and addendum V2b of `test/contracts/trust-gate-hardening.contract.md`).
This forbids `native_decide`, `bv_decide`, `sorry` and `admit`, and switching
`warningAsError` off in code. Code in the audited trees is object-level
(ruling R-V10, addendum V2c of the same contract): it declares no syntax,
macro or elaborator and runs no metaprogram outside the modules named on the
gate's exact `metaprogrammingModules` list. The gate refuses the keywords
that do so, and any other module's registration of a token, parser, syntax
category, macro, elaborator or initializer, however spelled. It also refuses
a token of the final token table that could hide a refused word, a
`(config := …)` whose value is not a literal brace group, any command of
`WhatwgTest.lean` other than its imports and the gate command, which comes
last, and an audited module that maps to no scanned source. Linters the gate
module registers check that the gate's own elaborator ran the root's gate
command, and run every pass when it did not. The gate's summary line reports,
per tree, how many declarations reach `Classical.choice`. The token rules are
lexical, and the contract's claim-scope sections (13, V2b.7 and V2c.7) list
what they do not catch. The gate code carries R-11 since commit `184d7fe`,
and R-V1, R-V2, R-V6 and R-V10 since the lane V landing.

The in-tree gate is a command inside the tree it audits, so code that runs
during elaboration can replace it. `lake exe whatwg_trustgate` runs the same
passes from outside (ruling R-W7): the passes are the library
`WhatwgGates/Trust/`, the lists are data in `WhatwgGates/TrustConfig.lean`,
and the executable reads the built modules without running any of their
code. It also refuses what the in-tree command cannot see: a stale or
missing `.olean`, a recorded option that differs from `lakefile.toml`,
`weakLeanArgs`, a `lakefile.lean`, and an audited module that writes to an
environment extension outside the allowlist. Section V2e.7 of the contract
lists what it does not catch.

## Generated facts and long-run continuity

Authored routers are never generated. Machine status, census rows,
declaration digests, obligation graphs, leaf receipts, and proof receipts are
generated from canonical inputs and checked for drift. A fresh session resumes
by reading, in order:

1. `PLAN.md` current-phase row;
2. `SPEC-MANIFEST.md` pins and open dispositions;
3. the current contract packet and counterexample rows;
4. the per-declaration assurance row;
5. the narrow verification command recorded by that row; and
6. `git status --short --branch` to attribute local changes.

## Handoff

Every handoff records base and head commits, file fence, changed files, exact
commands and results, public declarations, axiom output, open proof edges or
leaf receipts, counterexamples exercised, and whether any evidence is bounded
or host-only.
