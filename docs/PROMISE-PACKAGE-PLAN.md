# Promise layer reification plan

Status: Q0 landed on `main` 2026-09-06 at `652d29e` (pins) and `5e7a4e6`
(roots and ruling DB-11). Q1 through Q4 are open. This file owns the promise
lane: the census of ECMA-262's Jobs and Promise Objects clauses and of Web
IDL's promise and exception sections, the two libraries beneath Streams that
those censuses classify, and the first semantic packet over them.

The lane is the P8 entry under DB-11. It is not P8: P8's configuration,
bounded runner and WPT replay sit on top of what this lane builds, and the
held P8a draft on `codex/configuration-breaker` is restated against these
owners before it is unfrozen (slice Q4). The operator's 2026-09-05 semantics
hold was lifted for this lane only, and the breadth-before-depth rule applies
inside it: census and dispositions first, then a frozen packet, then
declarations.

## Purpose

Ruling DB-11 in `docs/DESIGN-BASIS.md` places ECMA-262's promise objects,
reaction and capability records and job queue in `Whatwg.Ecma262`, and the Web
IDL operations WHATWG algorithms use over them, plus the exception kinds, in
`Whatwg.WebIdl`. Both sit beneath every Stratum S library. The reason is
consumer count, not tidiness: the pinned Streams source invokes Web IDL
promise operations 197 times, and Fetch and the event loop will invoke the
same operations again. A promise layer usable without Streams is what DB-11
buys, and the accepted cost is restating the P8a draft's cell, token and
registration obligations against the new owners.

Nothing in this lane changes DB-03. The job queue stays deterministic FIFO
state inside the configuration, not a decision kind; what the lane adds is a
named home for that state and a census row for the requirement sentence it
realizes.

## Authorities

| Authority | Exact pin | Vendored bytes |
| --- | --- | --- |
| WHATWG Web IDL Standard | `whatwg/webidl` commit `a652053f1e74e4aaf647528deb174012ed6c909f`, "Review Draft Publication: March 2026"; `index.bs` SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`, 695,845 bytes; CC-BY 4.0 | `vendor/whatwg-webidl-a652053f/`, three files |
| ECMAScript Language Specification, ES2026 | `tc39/ecma262` commit `0248456c758431e4bb8e5d26333ff1865123c9cd` (tag `es2026`, 2026-03-31); `spec.html` SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`, 2,978,793 bytes; Ecma license | `vendor/ecma262-0248456c/`, three files |

`SPEC-MANIFEST.md` owns both pins, the authority order and the section
dispositions. `docs/PROVENANCE.md` owns the fetch commands, digest
cross-checks and licenses. `docs/ARCHITECTURE.md` owns the module boundaries.
`docs/SPEC-COVERAGE.md` owns the row kinds, the row format and the coverage
block. This file owns the lane's slices, entry and exit gates, file fences and
handoffs, and nothing else.

Two joined authorities are already pinned and censused: the Streams Standard
at `b9ba9f49` supplies the 197 invocation sites the Web IDL census joins
against, and the Infra Standard at `3f984adc` supplies the list and map
carriers the Web IDL algorithms use. Neither pin moves in this lane.

## Target library shape

Two roots and four modules, every one declaration-free today and reached from
`Whatwg.lean` and therefore from the root axiom gate:

```text
Whatwg/Ecma262.lean            root; imports Promise and Jobs
Whatwg/Ecma262/Promise.lean    promise state, capability and reaction records,
                               resolving functions, PerformPromiseThen
Whatwg/Ecma262/Jobs.lean       Job closures, the FIFO queue, NewPromiseReactionJob,
                               the HostEnqueuePromiseJob ordering requirement
Whatwg/WebIdl.lean             root; imports Promise and Exceptions
Whatwg/WebIdl/Promise.lean     "a new promise", "a promise resolved with",
                               "a promise rejected with", "resolve", "reject",
                               "react", the two "upon …", "wait for all",
                               "get a promise to wait for all", "mark as handled"
Whatwg/WebIdl/Exceptions.lean  simple exception kinds, the DOMException name
                               universe, "create" and "throw"
```

Import direction, fixed by DB-11 and unchanged by this plan:
`Whatwg.Ecma262` imports only `Whatwg.Infra`; `Whatwg.WebIdl` imports
`Whatwg.Ecma262` and `Whatwg.Infra`; `Whatwg.Streams` may import both and
neither may import it. `Whatwg.Streams` does not import them yet, and its
P4–P7 promise tables keep their current owners and proofs until Q4.

## Slice ledger

| Slice | Deliverable | Seat | Exit evidence |
| --- | --- | --- | --- |
| Q0 | the two pins, the two declaration-free roots, DB-11 | coordinator (landed) | `652d29e`, `5e7a4e6` on `main`; six vendored files blob-verified; vendor manifest regenerated; `docs/PROVENANCE.md`, `SPEC-MANIFEST.md`, `docs/ARCHITECTURE.md`, `docs/REIFICATION-STRATEGY.md`, `PLAN.md` record the pins and the ruling |
| Q1 | census tooling: the `Standard` profile refactor (R-P1), `Gates/Ecmarkup.lean`, the `webidl` and `ecma262` standards, two frozen breaker contracts and batteries, two CI steps | breaker, then two builders in their own worktrees (R-P7) | the Streams and Infra projections and rows modules byte-identical across the refactor; `lake exe census --standard webidl` and `--standard ecma262` PASS; both batteries green; `known-red.txt` empty again |
| Q2 | dispositions, dependency and external rows, the two coverage blocks | the two builders, then coordinator | every row resolves to exactly one disposition and every authored entry reaches a row, both directions; `dependencies.tsv` and `externals.tsv` complete and fully used; two all-`absent` coverage blocks emitted by Lean, quoted verbatim |
| Q3 | the first semantic packet, extraction-seeded (R-P12): first the inventory's move-and-generalize set — 6 moves and 28 generalizations out of `Whatwg.Streams` — landed with unchanged Streams proofs; then the gap set `G-01`–`G-11` that the six Web IDL promise operations and the ES2026 surface beneath them still require | extraction inventory seat (landed), then coordinator decisions, then breaker, then builder, then independent review | `docs/PROMISE-EXTRACTION-INVENTORY.md` landed before the freeze and every frozen ascription cites an `E-` row or a `G-` gap with its reuse mode; every existing Streams battery green with no P4–P7 statement, definition body or `attribute [local simp]` set changed; the root audit's declaration count moved by exactly the enumerated new abbrevs and bridging lemmas; declarations in the four modules; the FIFO realizer theorem under a named mask; census rows leave `absent`; axiom receipts inside R-11 |
| Q4 | the DB-11 restatement: P8a's obligations against the new owners, and the Streams promise tables as views | configuration breaker (unfrozen), then builder, then coordinator | conversion receipts relating `Readable.PromiseState`, `Writable.UnitPromise` and the `promises` slots to `Whatwg.Ecma262`; the three Streams `foreignBoundary` promise rows re-dispositioned as references; Streams coverage block re-emitted |

Q1 and Q2 are one breaker packet and two builder landings; they are separated
here because Q2's authored inputs are reviewable data that outlive the
generator change. Q3 does not start until Q2's coverage blocks exist, because
a packet that cannot name its census row ids cannot be joined.

## Q0 — pins and roots (landed)

**Seat.** Coordinator, main checkout.

**File fence.** `vendor/whatwg-webidl-a652053f/**`,
`vendor/ecma262-0248456c/**`, `generated/vendor-manifest.tsv`,
`Whatwg/Ecma262.lean`, `Whatwg/Ecma262/{Promise,Jobs}.lean`,
`Whatwg/WebIdl.lean`, `Whatwg/WebIdl/{Promise,Exceptions}.lean`,
`Whatwg.lean`, `SPEC-MANIFEST.md`, `docs/PROVENANCE.md`,
`docs/DESIGN-BASIS.md`, `docs/ARCHITECTURE.md`,
`docs/REIFICATION-STRATEGY.md`, `PLAN.md`, `COORDINATION.md`.

**Commands** (all exist today):

| Command | Decides |
| --- | --- |
| `lake exe vendorseal` | the two new trees and the manifest agree in both directions |
| `lake build` | the two roots and four modules elaborate and the root axiom gate reaches them |
| `lake exe citations` | no line-numbered citation into a protected authored document |

**Acceptance, met at `652d29e` and `5e7a4e6`.** Six vendored files sealed and
blob-verified, three per source; both roots imported from `Whatwg.lean`; zero
declarations in either tree, so neither owes a declaration record or a proof
graph (`docs/AGENT-ROUTING.md`).

**Open after Q0.** Everything below. A pin and a compiling scaffold are not a
census, a disposition, a declaration or a theorem.

## Q1 — census tooling

**Seats.** The promise census breaker in `promise/census-breaker` freezes both
contracts red in one packet. Then the Web IDL builder on `promise/webidl-census`
lands the profile refactor and the `webidl` standard; then the ES2026 builder
on `promise/ecma262-census` lands the ecmarkup scanner and the `ecma262`
standard on top of it. That order is R-P7 and it is not negotiable inside the
lane: the profile refactor touches `scanRequirements`, which produces the
seven Streams `requirement` rows the P7 work depends on.

**What the refactor is (R-P1).** `Gates.Census.Standard.definitionKeyed : Bool`
becomes a source profile. The Bikeshed profile carries per-scanner switches
`algorithmRows`, `definitionRows`, `idlRows`, `slotRows`, `requirementMarker`
and `sectionScope`, plus the heading levels the disposition walk admits. The
ecmarkup profile is served by a new `Gates/Ecmarkup.lean` scanner. The CLI
does not change shape: `lake exe census --standard <key>` keeps its three
modes.

Four repairs travel with the Bikeshed profile, each measured byte-neutral for
the two existing standards by the Web IDL survey and each re-checked by the
breaker's identity battery: key algorithm blocks on a `<div>` carrying an
`algorithm` attribute anywhere in the tag rather than on the byte prefix
`<div algorithm` (Streams 248 blocks under either rule, Infra 18 under either,
Web IDL gains the 45 that write `id=` first); take the IDL block openers from
the profile (`<xmp class="idl">` for Streams, `<pre class="idl">` and
`<pre class=idl>` for Web IDL) and repair three statement-level defects
(trailing `//` comments, `interface X : Base {`, `const` member names);
chunk the definition-span fallback on blank lines and read the Bikeshed dfn
type; and gate `scanRequirements` on `requirementMarker`.

Three decisions this plan takes inside R-P1's frame, because R-P1 fixes the
switch and leaves the input:

- **The section scope is authored data, not code.** The `sectionScope` switch
  names an authored `census/<key>/sections.tsv`, one heading id per line, read
  and checked like every other authored input: an id that matches no heading
  fails generation, and a scoped-out row that some authored entry claims fails
  generation too. Putting the whitelist in Lean would make a scope change a
  code review; putting it in `census/` makes it a data review, which is what
  the Web IDL survey's closing risk asks for when it says the whitelist is
  part of the frozen contract rather than a convenience.
- **Heading levels are a profile number, not a constant.** Web IDL writes its
  eleven promise operations under an `<h5>`; Streams and Infra have zero `<h5>`
  at line start, so raising the ceiling is byte-neutral for both and the
  alternative — eight authored per-row overrides — hides the section structure
  from the disposition walk.
- **Scope filtering is a predicate the scanners consult**, applied before the
  disposition join and before the duplicate check, so that the ten
  out-of-scope `<pre class="idl">` blocks of the Web IDL source never parse
  and never abort a run for reasons outside this lane.

**What the ecmarkup scanner is.** A second source shape, not a variant of the
first: ES2026 sections are `<emu-clause id type>`, operation names live only in
the structured `<h1>` (`aoid` occurs once in 22 operations), and `<emu-alg>`
bodies are indentation-nested `1. ` lines, not HTML lists. The scanner is
developed in parallel with the Web IDL builder as a pure scanner with its own
battery, and only then wired to a `Standard` record. Its refusal conditions are
the survey's R6 list, all vacuous at this pin and therefore cheap permanent
assertions: an `<emu-clause type>` outside the four observed values, a
`<dl class="header">` with a `<dt>` other than `description`, an `<emu-table>`
whose `<thead>` is not exactly three `<th>`, a body `<tr>` without exactly
three `<td>`, a `<dfn>` with neither id nor text, an `<emu-alg>` carrying
`replaces-step` or `example`, a step line not matching `^ *1\. `, an indent
that is not a multiple of two relative to the block minimum or that jumps more
than one level, an `&` inside a row span, and a scan cap hit.

**Row ids (R-P2, R-P3).** `Gates.Census.Kind` gains `builtin`, `hook`,
`property`, `record`, `field`, `term` and `clause`, used only by `ecma262`;
Web IDL uses the existing kinds, with definition rows disambiguated by
Bikeshed dfn type and `for`. Existing kinds and spellings are unchanged.
ES2026 ids derive from clause ids through an injective documented escaping
that preserves `.`, `%` and case, never `kebab`, which collides
`sec-promise.resolve` with `sec-promise-resolve`. Requirement bullets that
carry no id are positional within their clause and guarded by the span digest.

**File fence.**

| Tree | Owner in Q1 |
| --- | --- |
| `test/contracts/webidl-census.contract.md`, `test/contracts/ecma262-census.contract.md` | breaker, frozen |
| `WhatwgTest/Audit/WebIdl/CensusContract.lean`, `WhatwgTest/Audit/Ecma262/{CensusContract,EcmarkupContract}.lean`, the byte-identity battery for the two existing projections, `test/fixtures/trust-gate/known-red.txt` | breaker, frozen; a builder may repair elaboration, never a statement |
| `Gates/Census.lean` | the Web IDL builder first (profile refactor and the `webidl` record), then the ECMA-262 builder (the `ecma262` record only) |
| `Gates/Ecmarkup.lean` | the ECMA-262 builder |
| `census/webidl/**`, `census/ecma262/**` | builders (Q2 content, created here) |
| `generated/webidl-census.tsv`, `generated/ecma262-census.tsv`, `WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean`, `WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean` | generator output; never hand-edited, and named apart from the breaker's battery modules in the same directories |
| `.github/workflows/ci.yml` | coordinator at landing |

**Commands.**

| Command | Status | Decides |
| --- | --- | --- |
| `lake exe census` | exists today | the Streams census and the coverage emit against it are unchanged by the refactor |
| `lake exe census --report` | exists today | the Streams coverage block is unchanged, byte for byte |
| `lake exe census --standard infra` | exists today | the Infra census and its generated row list are unchanged |
| `lake exe census --standard webidl --write` | introduced by Q1 | writes `generated/webidl-census.tsv` and its rows module |
| `lake exe census --standard webidl` | introduced by Q1 | pin check and byte-drift check |
| `lake exe census --standard ecma262 --write` | introduced by Q1 | writes `generated/ecma262-census.tsv` and its rows module |
| `lake exe census --standard ecma262` | introduced by Q1 | pin check and byte-drift check |
| `lake build WhatwgTest.Audit.WebIdl.CensusContract` | introduced by the Q1 breaker packet | the Web IDL battery, red until the builder lands |
| `lake build WhatwgTest.Audit.Ecma262.EcmarkupContract WhatwgTest.Audit.Ecma262.CensusContract` | introduced by the Q1 breaker packet | the scanner and census batteries, red until the builder lands |
| `lake --wfail build Whatwg Gates vendorseal citations census urlinventory urlcensus` | exists today | production build with the CI warning policy |
| `lake --wfail build WhatwgTest` | exists today | the test root and the elaboration-time axiom gate |
| `lake exe vendorseal`, `lake exe citations`, `lake exe urlinventory`, `lake exe urlcensus` | exist today | the other gates stay green across the refactor |

`--report` is deliberately not introduced for either new standard. A standard
without a coverage numerator has no report today (Infra is the precedent), and
the CLI already refuses `--report` for such a key.

**Acceptance.**

1. `lake exe census`, `lake exe census --report` and
   `lake exe census --standard infra` all pass with the two existing
   projections and both rows modules byte-identical to their pre-refactor
   bytes. This is the identity the breaker freezes, and it is checked in the
   battery, not only by running the executables.
2. Both new censuses regenerate into a clean tree and compare byte for byte.
3. Every scanner refusal listed above fires on a synthetic input and none
   fires at the pin.
4. Row ids are unique, and `sec-promise.resolve` and `sec-promise-resolve`
   receive different ids.
5. `known-red.txt` is empty and no frozen statement changed.
6. Two CI steps are added, one per standard, beside the existing census steps.

**Open after Q1.** No disposition, no dependency row, no denominator and no
declaration. Row counts are a scanner fact, not coverage.

### Q1 ES2026 phase 1 receipt

**Seat.** ES2026 census builder, branch `promise/ecma262-census` in its own git
worktree, Windows x64, Lean 4.33.1. Base `37c2813` (`origin/promise/census-breaker`)
merged with `origin/main` as `c44b49d`, no conflict; the merge brought
documentation-only commits. Head at this receipt is the commit that carries it.

**Why this is a phase and not the slice.** R-P7 puts the profile refactor and
the `webidl` standard first, and at this receipt neither
`origin/promise/webidl-census` nor `origin/main` contains
`Gates.Census.Profile`. Phase 1 is therefore everything that can be built and
checked *without* editing `Gates/Census.lean`: the scanner, its own battery,
and the authored inputs. Phase 2 is the one-hunk wiring recorded at the end of
this receipt, and it is not started.

**File fence actually used.** `Gates/Ecmarkup.lean` (new),
`WhatwgTest/Audit/Ecma262/EcmarkupScanner.lean` (new), `census/ecma262/**`
(new: `sections.tsv`, `dispositions.tsv`, `overrides.tsv`, `rules.tsv`,
`dependencies.tsv`, `externals.tsv`, `README.md`), one import line each in
`Gates.lean` and `WhatwgTest.lean`, and this subsection. `Gates/Census.lean`,
every frozen contract and battery, `test/fixtures/trust-gate/known-red.txt`,
`COORDINATION.md`, `SPEC-MANIFEST.md`, `PLAN.md`, `vendor/`, `generated/` and
`Whatwg/` are untouched.

**Commands and their exact output lines.**

| Command | Output |
| --- | --- |
| `lake --wfail build Whatwg Gates` | `Build completed successfully (164 jobs).` |
| `lake build WhatwgTest.Audit.Ecma262.EcmarkupScanner` | `ecmarkup scanner: 49 clauses, 4 tables, 13 body rows, 9 requirement bullets, 390 step lines, 1 aoid, 9 dfn, 188 non-ASCII bytes over the two frozen windows of vendor/ecma262-0248456c/spec.html; 77 rows verified against the packet, 3 anchor lengths against Gates.Census.chooseAnchorLength` then `Build completed successfully (40 jobs).` |
| `lake build WhatwgTest` | fails on exactly the declared red set: `WhatwgTest.Audit.CensusProfileIdentity`, `WhatwgTest.Audit.WebIdl.CensusContract`, `WhatwgTest.Audit.Ecma262.CensusContract`. `WhatwgTest.Audit.Ecma262.EcmarkupScanner` is green. |
| `lake exe vendorseal` | `PASS vendor seal: manifest and vendor/ agree in both directions; every path is valid on Windows` |
| `lake exe citations` | `PASS internal citations: 309 files scanned; no line-numbered citation into a protected authored document` |
| `lake exe census` | `census: 450 rows (idl 133, op 248, requirement 7, rule 0, slot 62, type 0); dispositions (owned 260, requirement 8, foreignBoundary 42, hostOnly 100, refused 14, evidenceOnly 26, targetOnly 0); denominator 410, excluded 40; 0 IDL statement(s) outside the row vocabulary` then `PASS census (streams): …` |
| `lake exe census --standard infra` | `census: 176 rows (idl 0, op 150, requirement 0, rule 0, slot 0, type 26); dispositions (owned 157, requirement 4, foreignBoundary 4, hostOnly 0, refused 0, evidenceOnly 11, targetOnly 0); denominator 165, excluded 11; 0 IDL statement(s) outside the row vocabulary` then `PASS census (infra): …` |
| `lake exe census --report` | `WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;` / `green 12, partial 6, absent 392; census 450 rows, 40 excluded` |
| `lake exe urlinventory` | `PASS URL inventory: pinned bytes, full token partition, 1473 source candidates; projection is byte-identical` |
| `lake exe urlcensus` | `PASS URL census: pinned source, authored joins; both projections are byte-identical` |

The two existing censuses and the coverage block are unchanged, which is the
half of `test/contracts/census-profile-identity.contract.md` this phase must
not disturb; nothing in this phase touches the generator.

**Counts the scanner produces, all from the sealed bytes.** Over the two frozen
windows `sec-jobs` (624525..636548) and `sec-promise-objects`
(2686444..2746707): 49 `<emu-clause>` elements, 34 with a `type` attribute in
exactly the three admitted values, 1 `aoid`, 21 `<dl class="header">` with 10
`<dt>description</dt>` and no other `<dt>`, 4 `<emu-table>` with 13 body rows
of three cells each, 32 `<emu-alg>` blocks with 390 step lines at levels
0→175, 1→120, 2→74, 3→21 and no fourth level, 9 `<dfn>`, 9 requirement
bullets, 188 non-ASCII bytes, 0 tabs, 0 CR and 0 `&`.

The 77 rows come out as `builtin` 13, `clause` 8, `field` 8, `hook` 6, `op` 16,
`property` 3, `record` 3, `requirement` 9, `slot` 5, `term` 6, with `idl`,
`rule` and `type` zero — the per-kind table of section 6 of the packet. The
authored inputs join to `owned` 44, `foreignBoundary` 13, `hostOnly` 10,
`requirement` 7, `evidenceOnly` 3, denominator 74, split 31/7/6/2/3 over the 49
primary rows and 13/3/7/5/0 over the 28 sub-rows, which is the packet's
disposition table exactly. 52 disposition entries and 3 overrides are all used,
41 external identities are all used, and each of the 77 rows carries exactly
one dependency line whose every target is a row of this census or a declared
external. These are proposals until the coordinator ratifies them; no row is
anything but `absent` and nothing here is coverage.

**Deviations from the contract and the survey, and why.**

1. *The row-assembly function returns spans and ids, not rendered rows.*
   `Gates.Ecmarkup.rows : ByteArray → Array (Nat × Nat) → Except String (Array
   RowSpec)` gives each row a kind spelling, an id and a half-open span, and
   leaves the anchor, the span digest and the excerpt to
   `Gates.Census.chooseAnchorLength`, `Gates.Sha256.hexDigest` and
   `Gates.Census.renderRow`. The alternative was a second copy of the anchor
   ladder inside `Gates/Ecmarkup.lean`, because `Gates/Census.lean` must import
   this module to serve `Profile.ecmarkup` and the dependency cannot run both
   ways. One anchor ladder and one row-rendering rule in the repository is
   worth more than a literal reading of "produce the rows", and it is what
   makes the phase-2 wiring a single hunk. The handful of byte primitives the
   scanner does re-spell are documented as such in its module header.
2. *The packet's section 9 table is not in the generator's sort order.* Its 77
   rows are printed in a collated order in which `term.%Promise.prototype%`
   precedes `term.%Promise%` and both precede `term.job`. Lean's `String <` is
   ordinal, so the generator's sort key `kind.name ++ "|" ++ id` puts
   `term.%Promise%`, `term.%Promise.prototype%` and
   `term.Promise~20~prototype~20~object` before `term.job` and its two
   siblings. Only these six rows move, only among themselves, and the packet's
   own gate demands exactly the ordinal order — it requires the projection to
   be strictly increasing in that key and looks every frozen row up by
   `(kind, id)`. The battery asserts the ordinal order and the row set; no row,
   span, digest or anchor differs.
3. *The three anchor-length disagreements the breaker recorded against the
   survey are reproduced by the real generator, not merely accepted.* Running
   `Gates.Census.chooseAnchorLength` over all 77 spans of the pinned file
   returns the packet's histogram — 24 for 20 rows, 32 for 29, 48 for 26, 64
   for 1 and 256 for 1 — and every one of the 77 lengths equals the packet's.
   In particular `field.jobcallback-records.HostDefined` takes **256**, not the
   survey's 252: the survey's PowerShell re-implementation clamps a ladder rung
   to the span length and `chooseAnchorLength` does not. The shortest anchor in
   the lane is **24** (`term.%Promise%`), not the survey's 20, for the same
   reason: `baseWanted = min(bs.size - start, 24)` measures the rest of the
   file, never the span, so a 20-byte span still gets a 24-byte anchor. The
   survey's 20→1, 24→19, 32→26, 48→29, 64→1, 252→1 histogram is wrong in
   exactly the three places the packet says it is. That measurement is a
   one-off: `Gates.Census.occurrences` scans all 2,978,793 bytes for each
   probe, which the elaboration-time interpreter runs at about 3.5 seconds a
   row, so the whole pass took 269.8 s under `lake env lean --run` on a
   throwaway script and does not belong in a default build. The battery keeps
   three of the 77 permanently — the only 256 rung, the only 64 rung and the
   shortest anchor — and phase 2's compiled `lake exe census --standard
   ecma262` restores all 77.
4. *Two refusals the packet does not list are implemented, both stricter than
   it requires and both vacuous at the pin*: a tag with no element name inside
   a scanned window, and a `<dl class="header">` or `<dt>` that is never
   closed. Neither weakens a frozen refusal.

**Phase 2 wiring instructions.** In order, once `Gates.Census.Profile` exists
on `origin/promise/webidl-census` or `origin/main`:

1. *Merge, then replace the dispatch branch.* The Web IDL builder leaves one
   branch in `Gates.Census.build` reading
   `Except.error "profile ecmarkup: scanner not wired"`. Replace exactly that
   branch, and add `import Gates.Ecmarkup` to `Gates/Census.lean`:

   ```lean
   | .ecmarkup => do
       let mut windows : Array (Nat × Nat) := #[]
       for clauseId in sectionIds do
         windows := windows.push (← Gates.Ecmarkup.rootWindow bs clauseId)
       let specs ← Gates.Ecmarkup.rows bs windows
       let mut rows : Array Row := #[]
       for spec in specs do
         let some kind := Kind.ofString? spec.kind
           | .error s!"census: the ecmarkup scanner produced the unknown kind {spec.kind}"
         rows := rows.push
           { kind := kind, id := spec.id, anchorB := spec.b, anchorE := spec.b,
             spanB := spec.b, spanE := spec.e }
       pure (rows, 0)
   ```

   `sectionIds` is the `census/ecma262/sections.tsv` reader R-P1's
   `sectionScope` switch already needs; `rootWindow` is the only function in
   `Gates/Ecmarkup.lean` that reads outside a window, and it refuses a root id
   that does not occur exactly once. Everything after this hunk — the sort, the
   duplicate check, the anchor loop, the disposition join, `renderCensus` and
   `renderRowsModule` — is the existing shared path and needs no change.
2. *Add the `ecma262` standard* with exactly the field values the battery
   `WhatwgTest/Audit/Ecma262/CensusContract.lean` section 2 asserts:
   `key := "ecma262"`, `label := "ECMAScript ES2026 (0248456c)"`,
   `inputRelativePath := "vendor/ecma262-0248456c/spec.html"`,
   `inputDigest := "ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0"`,
   `censusRelativePath := "generated/ecma262-census.tsv"`,
   `rowsRelativePath := "WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean"`,
   `rowsNamespace := "WhatwgTest.Audit.Ecma262.SpecCoverageRows"`,
   `authoredDir := "census/ecma262"`, `profile := .ecmarkup`. The derived
   `regenerateCommand` must read `lake exe census --standard ecma262 --write`,
   and `sectionsRelativePath`, `dependenciesRelativePath` and
   `externalsRelativePath` must derive to `census/ecma262/sections.tsv`,
   `.../dependencies.tsv` and `.../externals.tsv`. Append it to
   `Gates.Census.standards` after `webidl`, so `standards.length == 4` and the
   Streams and Infra sort keys do not move.
3. *Authored-input readers the row assembly expects.* `sections.tsv` is one
   clause id per line, comments on `#`, read before the scan and turned into
   windows by `rootWindow`; a listed root that governs no row, and a row
   outside every window, both fail. `dispositions.tsv`, `overrides.tsv` and
   `rules.tsv` keep their existing formats and readers, with the section key
   resolved by the row's innermost enclosing clause — the file is authored so
   that a single innermost lookup suffices and an outward walk gives the same
   answer, so either implementation of `resolveDisposition` works.
   `dependencies.tsv` and `externals.tsv` are the URL lane's format and are
   read by the Web IDL builder's reader, unchanged. `rules.tsv` is present and
   entry-free; this standard emits zero `rule` rows.
4. *Generate and turn the battery green.* `lake exe census --standard ecma262
   --write` writes `generated/ecma262-census.tsv` (frozen header line, 77 rows)
   and `WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean` (`rowTotal 77`,
   `denominator 74`, the disposition counts above). Then
   `lake build WhatwgTest.Audit.Ecma262.CensusContract` must be green and its
   line removed from `test/fixtures/trust-gate/known-red.txt`, and
   `lake exe census --standard ecma262` must print `PASS` with `--write` in a
   clean tree leaving no diff. `--report` stays refused: this standard has no
   numerator.
5. *CI.* Add one step after the Web IDL census step of `.github/workflows/ci.yml`:

   ```yaml
   - name: ECMA-262 census
     run: lake exe census --standard ecma262
   ```

## Q2 — dispositions, dependency and external rows, coverage blocks

**Seats.** The two builders author their standard's inputs; the coordinator
reviews the dispositions against `SPEC-MANIFEST.md` and lands.

**Authored inputs.**

| File | Role |
| --- | --- |
| `census/webidl/sections.tsv`, `census/ecma262/sections.tsv` | the frozen section scope |
| `census/webidl/dispositions.tsv`, `census/ecma262/dispositions.tsv` | section-and-kind dispositions, seeded from the two new `SPEC-MANIFEST.md` tables |
| `census/webidl/overrides.tsv`, `census/ecma262/overrides.tsv` | per-row exceptions with a reason |
| `census/webidl/rules.tsv` | the six `idl-DOMException-derived-interfaces` requirement bullets, each with the optional end locator R-P4 adds |
| `census/ecma262/rules.tsv` | empty at Q2 unless the positional bullet ids of R-P3 need an authored anchor |
| `census/webidl/dependencies.tsv`, `census/ecma262/dependencies.tsv` | exactly one dependency list per row, in the URL lane's format |
| `census/webidl/externals.tsv`, `census/ecma262/externals.tsv` | the external identities those lists name |

**The four escape treatments (R-P6).** Web IDL's escapes split into the
`Whatwg.Ecma262` boundary — five operations (`Call`, `Construct`,
`CreateBuiltinFunction`, `NewPromiseCapability`, `PerformPromiseThen`) and
three intrinsics, which is the exact P8 surface — Infra dependency rows by
existing Infra row id, out-of-scope Web IDL sections as `hostOnly` dependency
rows naming their heading id, and HTML, DOM and realm machinery as externals.
ES2026's escapes split into a named ES2026 core boundary carrying Completion
Records, Abstract Closures and the object-model operations, and externals for
agents, realms and execution contexts.

`[=Queue a microtask=]` is flagged separately in the Web IDL externals: it is
a step of `wait for all`, so any ordering claim about that operation depends on
it, and it is the only external in group B that is not confined to the example
subsection.

**Commands.** As Q1, plus `lake exe census --standard webidl --write` and
`--standard ecma262 --write` re-run after each authored change.

**Acceptance.**

1. Every row resolves to exactly one disposition with no generator default,
   and every `dispositions.tsv`, `overrides.tsv`, `rules.tsv` and
   `sections.tsv` entry reaches at least one row. Both directions fail
   generation, as they do for Streams and Infra.
2. Exactly one dependency list per row; every external identity in
   `externals.tsv` is used; no dependency names a target that is neither an
   Infra row id, an in-lane row id, nor a declared external.
3. The disposition totals agree with the two new `SPEC-MANIFEST.md` tables.
   A disagreement is repaired in the authored input or in the manifest, never
   by relabelling a row to make a total come out.
4. Both coverage blocks emit all-`absent` from the Lean emit and are pasted
   verbatim into the landing record with their commit. No percentage is
   computed by hand and no count is quoted from this plan.
5. The two anchor-ladder rows the ES survey flags are checked against the real
   `Gates.Census.chooseAnchorLength` rather than against the survey's
   PowerShell re-implementation:
   `field.job-callback-record.host-defined` (span 629941..630193), unique only
   at its full 252 bytes, and `field.promise-capability-record.promise` (span
   2688749..2688997), the only row needing the 64-byte rung.

One expected count moves under R-P4 and is recorded so that a landed census
far from it is questioned rather than accepted. The Web IDL survey's expected
118 scoped rows count only `<dfn>`-tagged definitions; the three heading-borne
definitions the ruling admits — `Promise` on the `idl-promise` heading,
"exception objects" on `js-exception-objects`, and the `DOMException`
interface on `idl-DOMException` — are not among them, so the expected total is
121. ECMA-262's expected total is 77 with 74 in the denominator. The generated
censuses own both numbers.

**Open after Q2.** Every row is `absent`. No Lean declaration exists in either
library, so no coverage state can be anything else. `docs/PROMISE-DAG.md` is
opened here with its ten edges, all `required-open` except those the packet
declares `not-applicable` with a reason.

## The extraction inventory

Ruling R-P12 requires that the four modules be seeded by extraction from what
`Whatwg.Streams` already proves, never by fresh design, and that an extraction
inventory exist before the Q3 breaker freezes anything.
`docs/PROMISE-EXTRACTION-INVENTORY.md` is that inventory, authored 2026-09-06.
It owns, and this file does not restate: the 74 inventoried Streams
declarations with their ES2026 or Web IDL reading, target module, reuse mode
(6 move, 28 generalize, 40 keep), dependent-theorem counts and per-row risk;
the eleven-row gap table `G-01` through `G-11`; the six-level move ordering
with its definitional-equality argument; the P8a reuse classification of the
158 draft ascriptions; and twelve open decisions for the coordinator. Q3 and
Q4 below cite it by row id. A Q3 ascription that duplicates an inventoried
declaration without naming its row and reuse mode is a defect under R-P12.

## Q3 — the first packet, extraction-seeded

**Shape.** Q3 has two deliverables in order, and nothing else. The first is
the inventory's move-and-generalize set, landed with every existing Streams
proof unchanged. The second is the gap set: what the six Web IDL operations
and the ES2026 surface beneath them still require once the first deliverable
has been subtracted. Both are frozen in one breaker contract whose every
ascription cites either an inventory row id or a gap id.

**Deliverable 1 — the move and generalize set.** The 6 `move` rows (`E-01`
through `E-06`: `Readable.PromiseState`, `Readable.PullAnswer`,
`Readable.PullReturn` and the three `Writable` abbrevs over them) relocate to
`Whatwg.Ecma262.Promise`, and Streams keeps an `abbrev` at each old name. The
28 `generalize` rows land as a general declaration plus a bridging lemma, with
the Streams definition and its theorem statements untouched: the tables and
their operations (`E-13` through `E-23`), the reaction and registration
cluster (`E-29` through `E-33`, `E-37`, `E-38`), the three job queues and
their FIFO stages (`E-44` through `E-46`, `E-48` through `E-53`), the
settled predicate (`E-55`, `E-56`), and the exception universe (`E-59`).
The inventory's level order L0 through L6 fixes what precedes what; its
condition 3 fixes why no function named in an `attribute [local simp]` set is
a `move`.

**Deliverable 2 — the gap set.** Only what `G-01` through `G-11` name: the
split reaction lists, the handled bit's missing consumer, the capability
record and resolving functions, `IsPromise`, thenable adoption, the
`wait for all` operation as distinct from its settled predicate, the
realm-independent job queue, the run condition as a stated requirement, the
Web IDL exception universe beyond two kinds, the Completion carrier, and
`PerformPromiseThen` as a whole operation with a result capability. A frozen
ascription that is neither a deliverable-1 row nor a deliverable-2 gap does
not belong in this packet.

**The operations the two deliverables are measured against.** The Web IDL
operations that carry the Streams load, and the ES2026 operations they bottom
out in. Invocation counts are the Web IDL survey's, recomputed over all 2,188
whitespace-normalised `[=…=]` autolinks of the pinned Streams source. This
table is the target; deliverable 1 says how much of it Streams already has,
and deliverable 2 is the remainder.

| Web IDL operation | Row (id as the current naming ladder derives it) | Streams invocations |
| --- | --- | ---: |
| `a promise resolved with` | `op.a-promise-resolved-with` | 46 |
| `a promise rejected with` | `op.a-promise-rejected-with` | 46 |
| `resolve` | `op.resolve` | 35 |
| `reject` | `op.reject` | 23 |
| `a new promise` | `op.a-new-promise` | 18 |
| `react` | `op.dfn-perform-steps-once-promise-is-settled` | 8 |
| **subtotal, the six** | | **176** |
| `upon fulfillment` | `op.upon-fulfillment` | 9 |
| `upon rejection` | `op.upon-rejection` | 11 |
| **subtotal with the two wrappers** | | **196 of 197** |

The five operations above `react` are the 168 the survey names. Its sentence
"six operations carry the whole load … those six are 168 of 197" lists six
items whose counts sum to 188, because its sixth item is the two `upon …`
operations taken together; 168 is the subtotal of the five single operations.
The table above is the arithmetic, and no ruling depends on the difference.
`react` is the primitive the two `upon …` wrappers are defined over, so it is
on the critical path at eight direct invocations and the wrappers land beside
it rather than after it. The one remaining invocation is
`get a promise to wait for all`, in the pipe-to shutdown path; it and
`wait for all` are a P7-facing packet, and `mark as handled` has zero
invocations at this pin and stays an honest uncovered denominator row under
R-P4.

**The ES2026 surface underneath.** `NewPromiseCapability`
(`sec-newpromisecapability`, 2696238..2698770), `PerformPromiseThen`
(`sec-performpromisethen`, 2740635..2743669, 29 steps and the single most
important row in the lane), `CreateResolvingFunctions`
(`sec-createresolvingfunctions`, 2692679..2695411, 33 steps),
`FulfillPromise` and `RejectPromise` (2695419..2696230, 2699323..2700252),
`TriggerPromiseReactions` (`sec-triggerpromisereactions`, 2700260..2701212),
`IsPromise`, `NewPromiseReactionJob` (`sec-newpromisereactionjob`,
2702885..2705591, where the mask-M2 settlement-order theorem lives), the
PromiseCapability and PromiseReaction records with their eight fields, the
five promise instance slots, and the FIFO job queue as the realizer of
`HostEnqueuePromiseJob`.

Which half of that surface is extraction and which is gap is settled row by
row in the inventory, not here, and the split is uneven. Streams already has
`FulfillPromise`/`RejectPromise` in guarded form (`E-20`), `TriggerPromiseReactions`
as a fold over a reaction list (`E-33`), `PerformPromiseThen` steps 8 to 10
twice over (`E-31`, `E-37`), the five instance slots as first-order state
(`E-01`, `E-13`, `E-15`, `E-29`) and three FIFO job queues (`E-45`, `E-48`,
`E-52`). It has no PromiseCapability record, no resolving functions, no
`IsPromise` and no result capability at all (`G-03`, `G-04`, `G-11`), and it
splits no reaction list (`G-01`). `NewPromiseCapability` is therefore a gap
where `FulfillPromise` is an extraction, and the packet must not present them
as one uniform surface.

**The realizer theorem.** Under R-P5, `hook.host-enqueue-promise-job` and the
ordering bullet it carries are `requirement`, not `foreignBoundary`. The
bullet is the sentence at span 634739..634841 of the pinned `spec.html`, digest
`6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65`: jobs run
in the order of the invocations that scheduled them. The obligation is the
DB-05 shape already used for `ReadableStreamPipeTo`: state the requirement as
a specification over runs, state the deterministic FIFO queue in
`Whatwg.Ecma262.Jobs` as one candidate realizer, and prove that the realizer's
runs satisfy it. The theorem names its mask; the settlement order this lane
observes is M2 by DB-04, and any equational sub-law that observes no order
records that instead, per row.

The realizer half of that pair is extraction, and the specification half is
gap. Streams already has three deterministic FIFO queues with proved
dequeue-in-order laws — `Writable.tick_job_fifo` and `tick_no_job` (`E-45`,
`E-46`), `Readable.runPullJob_suspended`/`_empty`/`_cons` (`E-48`, `E-49`),
`Transform.tick_job_fifo` and `tick_no_job` (`E-52`, `E-53`) — each guarded by
its own spelling of "the execution context stack is empty" (`frames = []`,
`control = []`, and the transform's three-way guard). What does not exist is
the requirement itself: `G-08` records that the run condition appears only as
a hypothesis of a branch equation and never as a named specification over
runs, and `G-07` records that there is no single realm-independent queue for
one to be stated over. The builder therefore extracts the realizer from three
places and authors the specification once.

**Two boundaries the packet must declare before its first step.** Every one of
the 390 in-scope ES2026 steps is written in the completion discipline, with 53
`? ` and 9 `! ` prefixes that are early returns a Lean model reproduces
exactly, so a Completion carrier is admitted with the packet. The thirteen
Abstract Closures the in-scope algorithms create are first-order descriptors —
a tag plus the capture list the source states explicitly — never Lean
functions, per the representation rules. Both sit inside R-P6's named ES2026
core boundary; see the open decisions below for what that phrase leaves
unsettled.

**Seats.** The extraction inventory seat lands
`docs/PROMISE-EXTRACTION-INVENTORY.md` first; R-P12 makes it a precondition of
the freeze, not a parallel task. The coordinator then answers the inventory's
twelve open decisions, because five of them (the state's type parameters, the
reason parameter, the identity type, the job payload parameter, and move
versus generalize for the eleven functions named in `attribute [local simp]`
sets) fix signatures the contract cannot ascribe without them. Then a breaker
in its own worktree freezes `test/contracts/promise-core.contract.md` and a
red battery under `WhatwgTest/Ecma262/` and `WhatwgTest/WebIdl/`; then a
builder; then independent review; then the coordinator lands with all gates.

**File fence.**

| Tree | Owner |
| --- | --- |
| `docs/PROMISE-EXTRACTION-INVENTORY.md` | extraction inventory seat, landed before the freeze; read-only for the breaker and the builder, and amended only by the coordinator recording decision answers |
| `test/contracts/promise-core.contract.md`, `WhatwgTest/Ecma262/**`, `WhatwgTest/WebIdl/**`, the `WP-*` rows of `test/counterexamples/REGISTER.md`, `test/counterexamples/promise/ATTACKS.md`, `test/fixtures/trust-gate/known-red.txt` | breaker, frozen |
| `Whatwg/Ecma262/{Promise,Jobs}.lean`, `Whatwg/WebIdl/{Promise,Exceptions}.lean` | builder |
| the `abbrev`s and bridging lemmas the move and generalize rows add inside `Whatwg/Streams/**` | builder, additive only; no existing Streams definition body and no existing Streams theorem statement may change |
| `docs/PROMISE-DAG.md` declaration and statement rows | breaker; the coordinator answers ruling requests there |
| `census/webidl/**`, `census/ecma262/**` coverage-bearing overrides | builder, with coordinator review |
| `WhatwgTest/Audit/WebIdl/SpecCoverage.lean`, `WhatwgTest/Audit/Ecma262/SpecCoverage.lean` | authored numerators, added here |

**Commands.**

| Command | Status |
| --- | --- |
| `lake build WhatwgTest.Ecma262.PromiseContract WhatwgTest.WebIdl.PromiseContract` | introduced by the Q3 breaker packet |
| `lake build Whatwg.Ecma262 Whatwg.WebIdl` | exists today (the roots exist; the target is empty until Q3) |
| `lake build Whatwg.Streams` and the P4–P7 batteries under `WhatwgTest/Streams/**` | exist today; they decide that the move and generalize set changed no Streams proof |
| `lake --wfail build WhatwgTest` root audit line | exists today; its declaration count decides that only the new abbrevs and bridging lemmas were added |
| `lake exe census --standard webidl`, `lake exe census --standard ecma262` | introduced by Q1 |
| `lake build`, `lake --wfail build WhatwgTest`, `lake exe vendorseal`, `lake exe citations` | exist today |

**Acceptance.**

1. Every frozen ascription elaborates and every frozen theorem is proved with
   no edit to a frozen statement, and every frozen ascription cites either an
   inventory row id (`E-01` … `E-74`) or a gap id (`G-01` … `G-11`). An
   ascription that cites neither, or that restates an inventoried declaration
   without naming its reuse mode, is a defect under R-P12 and the packet does
   not freeze.
2. Deliverable 1 landed with unchanged Streams proofs: every existing
   battery under `WhatwgTest/Streams/**` is green, no P4–P7 theorem statement
   changed, no Streams definition body changed, no `attribute [local simp]`
   set in `Readable/Reentrancy.lean`, `Writable/Lifecycle.lean`,
   `Transform/Runs.lean` or `Piping/Runs.lean` changed, and the root audit's
   declaration count differs from its pre-packet value by exactly the number
   of new abbrevs and bridging lemmas, enumerated in the landing record.
3. Deliverable 2 is bounded by the gap table: every declaration in the four
   modules that is not the target of a move or generalize row names the gap it
   closes, and no gap row is closed silently.
4. Axiom receipts for every exported theorem are inside the R-11 ceiling
   (`propext`, `Quot.sound`, `Classical.choice`); `sorryAx`,
   `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and the
   `native_decide` auxiliaries appear nowhere.
5. Each new exported declaration has one declaration record with its
   specification anchor, that anchor's span digest, its disposition and its
   duplicate-prevention relationship, and the generated declaration snapshot
   joins each to exactly one record. A declaration that realizes a move or
   generalize row names that row as its duplicate-prevention relationship.
6. The realizer theorem is stated and proved under its named mask, and its row
   leaves `absent`.
7. Both coverage blocks are re-emitted and pasted verbatim; rows that stayed
   `absent` are still `absent`, and no row is `green` with a step left to a
   boundary row.
8. `known-red.txt` is empty; independent review checks model intent, proof
   trust, spec fidelity and claim scope, and checks the inventory join in both
   directions: every frozen ascription reaches a row or gap, and every move and
   generalize row reaches a frozen ascription or is explicitly deferred with a
   reason.

**Open after Q3.** The four combinators and their iterator boundary, the
`then`/`catch`/`finally` built-ins beyond what `react` needs (`G-11`'s
remainder), `wait for all` and its microtask dependency (`G-06`), the
`DOMException` name universe (`G-09`'s remainder), the thenable job (`G-05`),
and everything P8 owns above this layer. Which gap rows Q3 closes and which it
defers is recorded in the landing record against the gap ids, so a deferral is
visible rather than silent.

## Q4 — the DB-11 restatement

**What is restated.** The held P8a draft on `codex/configuration-breaker`
(checkpoint `6c44e08` plus uncommitted drafts) was designed as an adapter
inside Streams: one actual writable root, observer registrations, and a global
FIFO of job references. DB-11 gives those three things owners outside Streams,
so the draft's cell, token and registration obligations are restated against
`Whatwg.Ecma262.Jobs` and `Whatwg.Ecma262.Promise` before the packet is
unfrozen. The identity, FIFO, effect-order, replay, progress and independent
source-prefix obligations named in `PLAN.md` remain open and are carried over
unchanged in content.

**The restatement is a re-homing, not a rewrite.** The inventory's P8a reuse
table classifies all 158 ascriptions the draft carries on disk (104 in
`OrderingContract.lean`, 54 in `OrderingLaws.lean`; that worktree's
`docs/CONFIGURATION-DAG.md` still records the earlier 102 and 44). Eight are
already general and change only their namespace: `Job` with its three
accessors, `enqueueJob`, `queuedJobs` and the two `_eq` laws over them.
Thirty-two need renaming only, their statements unchanged up to an abstracted
payload parameter: `PromiseRef`, `ObserverPhase`, `Registration` and `Active`
with their constructors and accessors, `lookup`, `lookupRegistration`,
`setRegistrationPhase`, `register` (Web IDL `react`), `notifySettled`
(`TriggerPromiseReactions`) with their five `_eq` laws, and the two FIFO-suffix
laws `step_active_jobs_eq` and `episodePrefix_jobs_eq`, the second being the
`active_episode_fifo_suffix` obligation R-P12 names. The remaining 118 are
Streams-specific adapters that stay in `Whatwg.Streams.Semantics` in content
as well as in file: `Config`, `Decision`, `Startup`, `JobKind`, `Event`,
`liftWritable`, `takeSinkHead`, `tick`, `decide`, the run judgments, the live
M2 view, the successful-control grammar, and the 45 laws over them. Q4 works
from that table; it does not re-derive the classification and it does not
reopen a draft ascription the table leaves alone. If Q3 lands inventory rows
`E-29` through `E-33`, `E-37` and `E-38`, the draft's registration cluster
becomes a use of the shared layer rather than a second design, and most of the
restatement cost DB-11 accepts is paid inside Q3.

**What becomes a view.** `Readable.PromiseState`, `Writable.UnitPromise` and
the `promises` slots keep their P4–P7 owners and proofs until this slice, and
then become views onto the shared layer with conversion receipts, not a second
owner. Each conversion is a named theorem in the P4–P7 declaration records'
duplicate-prevention relationship, changing those records from `canonical` to
`view` with the shared owner named. The conversions are not new work: the
inventory's rows `E-07` through `E-12` record that
`Writable.unitPromiseToShared`, `unitPromiseFromShared`,
`sinkAnswerToShared`, `sinkAnswerFromShared`, `sinkReturnToShared` and
`sinkReturnFromShared`, with their eighteen `_eq` and roundtrip receipts, are
already exactly those conversion theorems and survive Q3's moves by
definitional equality.

**The one existing denominator this lane touches.** R-P5 says the promise
instance slots are `owned` in the ES2026 census while the Streams census keeps
them `foreignBoundary`, and that the Streams rows become references into
`Whatwg.Ecma262` when P8 opens. That re-disposition is a Q4 change to
`census/overrides.tsv` and to the "Foreign internal slots" paragraph of
`census/README.md`, and it re-emits the Streams coverage block. Until Q4 it
does not happen: two censuses describing two libraries is the ruled reading,
and the Streams rows stay exactly as P1 landed them.

**Commands.** `lake exe census`, `lake exe census --report`,
`lake exe census --standard webidl`, `lake exe census --standard ecma262`,
`lake build`, `lake --wfail build WhatwgTest`, and the four other gate
executables. All exist today except the two introduced by Q1.

**Acceptance.** Conversion receipts for all three Streams promise tables; no
P4–P7 theorem statement changed; the Streams coverage block re-emitted and
quoted verbatim; the P8a packet frozen by its own breaker against the new
owners, with every restated ascription joined to its class in the inventory's
P8a reuse table and every one of the 118 adapter ascriptions carried over
unchanged; `COORDINATION.md` records the release of the configuration-breaker
hold.

**Open after Q4.** P8 itself: the configuration, the mask projections, the
bounded runner, the WPT replay harness against the three local host profiles,
and the host-profile refusal rows. This lane ends where P8's exit gate begins.

## Survey decisions and the rulings that answer them

Both surveys close with an explicit list of decisions for the coordinator.
The rulings R-P1 through R-P7 in `COORDINATION.md` answer almost all of them.
The table records the answer, not a re-argument; a ruling is not reopened here.

### ECMA-262 survey, section 7

| # | Decision | Answer |
| --- | --- | --- |
| 1 | extend the kind vocabulary or reuse the existing six | **R-P2**: extend, with `builtin`, `hook`, `property`, `record`, `field`, `term`, `clause` used only by `ecma262`; existing kinds and spellings unchanged |
| 2 | how `Standard` grows to a third source shape | **R-P1**: `definitionKeyed` becomes a profile with per-scanner switches plus an ecmarkup profile; the two existing projections stay byte-identical and the breaker freezes that identity |
| 3 | are the promise slots `owned` here while `foreignBoundary` in Streams | **R-P5**: yes, explicitly; the two censuses describe two libraries, and the Streams rows become references into `Whatwg.Ecma262` at Q4 |
| 4 | `HostEnqueuePromiseJob` as `requirement` or `foreignBoundary` | **R-P5**: `requirement`, realized by the FIFO queue in `Whatwg.Ecma262.Jobs` under DB-03, the same specification/realizer pattern as `ReadableStreamPipeTo`; `HostEnqueueTimeoutJob` and `HostEnqueueGenericJob` stay `foreignBoundary`, and the survey's `foreignBoundary` for the two hook requirement bullets stands |
| 5 | how the nine requirement bullets are identified | **R-P3**: positional within their clause, guarded by the span digest |
| 6 | `sec-promise-objects`' state vocabulary `evidenceOnly` or `owned` | **R-P5**: the survey's proposal stands, so `evidenceOnly`, and the ruled totals (44 `owned`, 13 `foreignBoundary`, 10 `hostOnly`, 7 `requirement`, 3 excluded) depend on it |
| 7 | which escape treatment applies to the object-model group | **R-P6**, partly: Completion Records, Abstract Closures and the object-model operations are one named ES2026 core boundary; agents, realms and execution contexts are externals. See the open items below for the four groups R-P6 does not name |
| 8 | census first, or a contract for the scanner first | **R-P7**: breaker first, both contracts frozen red in one packet |

### Web IDL survey, section 6

| # | Decision | Answer |
| --- | --- | --- |
| 6.1 | `scanRequirements` is hard-wired to the piping marker | **R-P1**: `requirementMarker` becomes a profile field, and the breaker freezes byte-identity of the Streams projection, which is what protects the seven P7 requirement rows |
| 6.2 | `idl-promise` `owned` or `hostOnly` | **R-P4**: `hostOnly`. This overrides the survey's recommendation of `owned`; the promise operations in `js-promise` are `owned` over a type whose row sits in the binding layer |
| 6.3 | `mark as handled` with zero Streams consumers | **R-P4**: `owned`, and it stays an honest uncovered denominator row |
| 6.4 | the six derived-interface bullets have no separable span | **R-P4**: `rules.tsv` gains an optional end locator so the six get disjoint spans |
| 6.5 | the four duplicate ids and the dfn-type naming policy | **R-P2**: Web IDL definition rows are disambiguated by Bikeshed dfn type and `for`. Under the survey's own row count the 28 `const`, `attribute` and `constructor` dfns fold into the IDL-block rows, which removes the four collisions. Residual, recorded not reopened: the folded attribute-getter steps then have no anchored span of their own |
| 6.6 | three definitions carry no `<dfn>` tag | **R-P4**: heading-borne definitions (`<h3 id=… interface>` and the bare `dfn` attribute) are definition rows, so `Promise`, "exception objects" and `DOMException` each get one |
| 6.7 | `scanSlots` on or off | **R-P4**: off for Web IDL; the promise internals it would have anchored at incidental use sites become `Whatwg.Ecma262` dependency rows |
| 6.8 | scope filtering inside the scanners rather than after them | **R-P1**: `sectionScope` is a profile switch; this plan applies it as a predicate the scanners consult, before the disposition join and the duplicate check |
| 6.9 | Bikeshed autolinks wrap across lines | No ruling needed. It is a measurement rule, not a decision: any join of Streams usage to Web IDL definitions normalises whitespace inside `[=…=]`, or it undercounts the two most-used operations by 12 |
| 6.10 | `Whatwg/WebIdl/Promise.lean`'s docstring cites a rule the pin does not state | Already repaired: the stub now names the ten operations and cites the survey, and reserves no "handled" rule |
| 6.11 | the router bookkeeping the survey did not do | **R-P7** plus this lane's plan seat: this file, the two `SPEC-MANIFEST.md` tables, the `docs/SPEC-COVERAGE.md` kinds and blocks, `census/README.md` and `docs/research/README.md` are one change by one seat, so no two files claim the same fact |
| 6.12 | the section whitelist is part of the frozen contract | **R-P1** plus this plan's `sections.tsv` choice: the whitelist is authored data inside the breaker's frozen input interface, and widening it is a contract change |

### Still open

Five items have no ruling: four decisions the surveys raise and that R-P1
through R-P7 do not reach, and one reading of R-P6 that the ruling's wording
leaves ambiguous. Each is deferrable, and the reason is stated, because a
deferral without one is a gap.

1. **The per-standard algorithm-name-first naming flag.** The Web IDL survey
   shows that preferring the block's `algorithm` attribute over its first
   `<dfn>` id turns `op.dfn-perform-steps-once-promise-is-settled` into
   `op.react` and `op.waiting-for-all-promise` into a readable name, and that
   this is *not* byte-neutral for Streams, so it must be a per-`Standard`
   flag. R-P1 enumerates six switches plus heading levels and does not
   include it. Deferrable only as far as Q1's landing: a row id is stable for
   the life of the census, so the flag is decided before
   `lake exe census --standard webidl --write` runs for the first time, and
   until it is, this plan cites the ids the current ladder derives.
2. **The four escape groups R-P6 does not name.** The ES2026 survey proposes a
   named "iterator tape" boundary for the combinators, externals for
   intrinsics and for error objects, a conventions record for the List type
   and the nine `~enum~` spellings, and out-of-lane dependency rows for the
   two hooks named but not called. R-P6 names only the core boundary and the
   agent externals. Deferrable: none of the four is reached by a Q3 row. The
   iterator tape belongs to the four combinators, which Q3 does not touch; the
   error-object external is not needed while a throw completion carries an
   error kind whose universe `Whatwg.WebIdl.Exceptions` owns under R-P4; the
   conventions record is admitted with the Completion carrier at the top of
   Q3; and the two out-of-lane hooks have no in-scope call site. All four are
   decided at Q2 when `externals.tsv` is authored, which is before any of them
   can be silently skipped.
3. **`idl-DOMException-derived-predefineds`: `hostOnly` or `evidenceOnly`.**
   The Web IDL survey marks this section for ratification because
   `QuotaExceededError` is the worked instance of the six requirements above
   it. R-P4 rules the binding layer `hostOnly` but does not name this section.
   The plan carries the survey's `hostOnly` and flags it. Deferrable: the
   choice moves rows between the denominator and the excluded set of a census
   that is all-`absent` until Q3, and no Streams algorithm reaches the name.
   It is decided at Q2 with the rest of the dispositions.
4. **Whether the 32 `DOMException` name rows stay 32 rows or become one
   enumeration row.** The survey asks; no ruling answers. Deferrable for the
   same reason as item 3, and decided at Q2. The 25 names no standard in this
   repository reaches are the whole of the question.
5. **What "named ECMA-262 core boundary" covers.** R-P6 groups Completion
   Records, Abstract Closures and the object-model operations into one
   category. The survey treats them differently and says so at length: the
   object-model operations reach arbitrary user code and are a boundary in the
   DB-02 sense; the thirteen Abstract Closures become first-order descriptors
   and stay `owned`; and Completion Records are explicitly *not* a boundary,
   because all 390 in-scope steps are written in the completion discipline and
   53 of them are `? ` early returns a Lean model must reproduce exactly.
   Recorded, not reopened: this plan reads the ruling as fixing where an
   escaping reference is *recorded* — one dependency category in
   `dependencies.tsv` — and not as fixing a row's disposition, which R-P5
   owns and which gives no in-scope row `foreignBoundary` for a completion
   reason. Under the stronger reading every ECMA-262 `op` row is permanently
   `partial` and Q3's fourth acceptance condition is unreachable, so the
   coordinator confirms the reading before the Q3 breaker freezes, and Q2's
   `externals.tsv` review is the natural place to do it.

## What this plan does not decide

No Lean declaration follows from this document. The census row counts, the
exact row ids, the kind constructors' spellings and every disposition wait for
their owning process: the Q1 breaker packet, then the two builders' authored
inputs, then the coordinator's review. The four modules stay declaration-free
until the Q3 packet is frozen. No number in this file is a coverage claim;
coverage is the block printed by `lake exe census --standard <key> --report`,
which does not exist for either standard until a numerator does.
