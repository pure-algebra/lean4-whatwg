# Receipts log of `CONFIGURATION-PG-ORDERING`

This log holds the history of `docs/CONFIGURATION-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/CONFIGURATION-DAG.md`.

## Configuration ordering proof graph (`CONFIGURATION-PG-ORDERING`, P8a / slice Q4)

Moved verbatim from the status paragraph under the title of `docs/CONFIGURATION-DAG.md` at `325d5d5`; a current status paragraph replaces it there.

Status: **frozen red**, 2026-09-07, by the Q4 restatement breaker seat.
Contract: `test/contracts/configuration-ordering.contract.md`.
Base: `main` at `f700230`. Branch `promise/q4-breaker`.

## Ten edges

Moved verbatim from `docs/CONFIGURATION-DAG.md` at `325d5d5`.

| Edge | Status | Required work |
| --- | --- | --- |
| identity | required-open | the exact declaration freeze this packet states; canonical address views; stable registration and job names; the generated declaration join. The 15 class [R] ascriptions elaborate today and are the only part delivered |
| construction | required-open | CFG-START, CFG-CELLS, CFG-TOKENS, CFG-STACK and inductive reachable-state preservation |
| semantics | required-open | CFG-EFFECTS, CFG-FIFO, CFG-RUNS, the foreign profile, the global scheduler and the live frontiers |
| laws | required-open | the 54 restated law ascriptions, the 15 Q4-owned bridging receipts and the 18 deferred-generalization ascriptions, each under the mask its docstring names |
| representation | required-open | one cell and payload owner, typed references, no closures and no shadow scheduler or table; the four view record rows of contract §4.1 and their twenty elaborating ascriptions |
| counterexamples | required-open | the actual configuration witness, the stable registered scheduler mutants and the retained failing alternatives. No WS-CONFIG id is frozen by this packet; `test/counterexamples/REGISTER.md` is outside its fence |
| bridges | required-open | CFG-LOCAL, CFG-OBS, CFG-WPT, CFG-HOST and the full P4/P5/P6/P7 embeddings; the three Q4 views and the four deferred generalizations are the part this packet states |
| targets | not-applicable | this graph generates no target program; P11 owns target lowering |
| trust | required-open | independent design review, the frozen red battery (delivered), the proofs, the 82 axiom receipts inside the R-11 ceiling, and the narrow, default and gate builds |
| coverage | required-open | the exact clause and numerator joins. This packet changes no coverage state: contract §7.4 recomputes the Streams totals and every one is unchanged, and §7.6 records that no frozen number moves |

`targets` is the only permanently not-applicable edge. No edge is closed by a
compiling battery alone, and none is closed by this freeze.

## Q4 landing, 2026-09-07, branch `promise/q4-builder`

Moved verbatim from `docs/CONFIGURATION-DAG.md` at `325d5d5`.

Appended by the Q4 builder seat. **Every row above this section is unchanged.**
No edge closes here: the landing is partial, four of the five batteries stay
declared red, and a compiling implementation is not a closed edge. Receipt: the
"Q4 landing receipt" of `docs/PROMISE-PACKAGE-PLAN.md`, which carries every
command and its result line; the four blocking items are §11.1 of the contract.

| Edge | Status before | Status at this landing | What moved |
| --- | --- | --- | --- |
| identity | required-open | **required-open**, unchanged | The 15 class [R] ascriptions elaborate against the landed `Whatwg.Ecma262` names, with the single exception of `Reaction.mk` (item B1: five arguments ascribed, six landed). No generated declaration snapshot exists, so the edge's own item is untouched |
| construction | required-open | **required-open**, unchanged | `E-22`'s three operations, five rewritten bodies and three table bridges landed, so `Readable.State.readPromises` is no longer a table without operations; CFG-START, CFG-CELLS, CFG-TOKENS, CFG-STACK and reachable-state preservation are untouched |
| semantics | required-open | **required-open**, unchanged | `tick`, `decide`, `takeSinkHead`, `Step`, `Reaches` and `EpisodePrefix` exist and their frozen equations are proved, and `runCondition_iff` reaches `Jobs.RunCondition` through `activeErase`. CFG-EFFECTS, CFG-FIFO's source-specific half, CFG-RUNS, the foreign profile, the global scheduler and the live frontiers stay open |
| laws | required-open | **required-open**, and most of it delivered | 50 of the 54 restated law ascriptions and 11 of the 12 Q4-owned bridging receipts are proved; all 18 deferred-generalization ascriptions are proved. The four that are not are B1 to B4. `OrderingLaws.lean` fell from 327 diagnostics to 4 |
| representation | required-open | **required-open**, and the record change landed | The four view record rows of contract §4.1 read as frozen in `docs/READABLE-DAG.md`, `WRITABLE-DAG.md` and `TRANSFORM-DAG.md`, and the twenty ascriptions of §4.2 still elaborate. One cell owner, one payload owner, no shadow scheduler and no second table: `Writable.State.promises` read through `Writable.promiseTable` is the only outcome table the calculus touches |
| counterexamples | required-open | **required-open**, unchanged | No configuration witness, no registered scheduler mutant and no WS-CONFIG row is landed by this seat |
| bridges | required-open | **required-open**, and the Q4 halves landed | The three Q4-owned views `jobQueue`, `reactions` and `activeErase` exist with their receipts; the four deferred generalizations of contract §5 are all proved, which makes `WhatwgTest/Streams/PromiseBridgeQ4.lean` green. CFG-LOCAL, CFG-OBS, CFG-WPT, CFG-HOST and the full component embeddings stay open — CFG-WPT was not attempted at all |
| targets | not-applicable | **not-applicable**, unchanged | This landing generates no target program |
| trust | required-open | **required-open**, partially delivered | 79 of the 82 named receipts print, all inside the R-11 ceiling: 14 empty, 27 `[propext]`, 33 `[propext, Quot.sound]`, 5 `[propext, Classical.choice, Quot.sound]`. `lake exe trustselftest` passes in both directions against a four-module declared red set. Independent review is not done and the three missing receipts are B3 and the two §6 laws |
| coverage | required-open | **required-open**, unchanged | R-P5's re-disposition landed and no coverage state moved: the two rows are `owned` and still `absent`, the Streams block re-emits byte-identically, and all four census standards pass |

**Edges closed at this landing: none. Edges reopened: none.**

## Q4 amendment, 2026-09-07, branch `promise/q4-amend`

Moved verbatim from `docs/CONFIGURATION-DAG.md` at `325d5d5`.

Appended by the Q4 amendment breaker seat. **Every row above this section is
unchanged**, including the landing table. No edge closes and none reopens: a
breaker amendment states, it implements nothing, and four of the five declared
batteries stay red by design. Receipt: §12.6 of
`test/contracts/configuration-ordering.contract.md`.

What the amendment changes about the edges' *required work*, without changing
any status:

| Edge | What the amendment changes about what is owed |
| --- | --- |
| identity | `Reaction.mk`'s ascription now matches the landed six-argument constructor, so all 15 class [R] ascriptions elaborate again; item B1 of the landing table is answered |
| laws | four of the 54 + 12 are answered, three by R-P25's text (A1 to A3) and one by restatement (A4). The Q4-owned receipt count rises from 12 to 15 |
| bridges | `CFG-WPT` is now split explicitly: the certificate carriers, the four checkers, the erasure and its two laws are Q4's and are stated; the existence half `run_erases_to_reference` is P8's, together with the transcription gate, the host replay and the mutants' register rows. The edge stays open on the P8 half |
| trust | 82 named receipts become 93. 79 print, all inside R-11; the 14 that do not are the names the second builder pass supplies. A fifth module, `WhatwgTest.Audit.CensusProfileIdentity`, is declared red for the reason decision 13 records, and the trust gate's all-green control stays unrestored |
| counterexamples | one row is seeded, `WS-PROM-CE-039`, against the packet's own false bridge. Its `test/counterexamples/REGISTER.md` entry is owed at landing; no `WS-CONFIG` id is frozen |

The other five edges are untouched by the amendment.

## Q4 landing, second pass, 2026-09-07, branch `promise/q4-builder-2`

Moved verbatim from `docs/CONFIGURATION-DAG.md` at `325d5d5`.

Appended by the Q4 builder seat, second pass. **Every row above this section is
unchanged**, including the first landing table and the amendment table. Receipt:
the "Q4 landing receipt (second pass)" of `docs/PROMISE-PACKAGE-PLAN.md`, which
carries every command and its result line.

**No edge closes here either.** All five declared batteries are green, the 93
receipts print inside R-11 and `test/fixtures/trust-gate/known-red.txt` is
empty — and none of that closes an edge, because a compiling battery closes no
edge and this packet proves no `WellFormed`, no progress theorem and no host
relation.

| Edge | Status before | Status at this landing | What moved |
| --- | --- | --- | --- |
| identity | required-open | **required-open**, unchanged | All 15 class [R] ascriptions elaborate, item B1 answered by A1. Two Q4-owned views are added, `phaseErase` and `reactionErase`, and 86 `Source` names. No generated declaration snapshot exists, so the edge's own item is untouched |
| construction | required-open | **required-open**, unchanged | Nothing new. CFG-START, CFG-CELLS, CFG-TOKENS, CFG-STACK and reachable-state preservation stay open |
| semantics | required-open | **required-open**, unchanged | `notifySettled_queued_serial` ties a triggered registration's phase payload to the serial of the `.observer` token the same notification appended, under mask M2 — the first statement in this packet that relates the two supplies of decision 2 through the queue. CFG-EFFECTS, CFG-FIFO, CFG-RUNS, the foreign profile, the global scheduler and the live frontiers stay open |
| laws | required-open | **required-open**, and fully delivered as stated | All 54 restated law ascriptions and all 15 Q4-owned bridging receipts are proved, and all 18 deferred-generalization ascriptions were already. B1 to B4 are answered by A1 to A4. `OrderingLaws.lean` and `OrderingContract.lean` are at zero diagnostics. The edge stays open on the obligations §3.3 lists, which no law here states |
| representation | required-open | **required-open**, unchanged | The `Source` judgment adds no cell and no table: `Certificate`, `Binding` and `ReferenceEvent` are immutable source-side data, and `referenceErase` is a `List.filter`. Still one cell owner, one payload owner, no shadow scheduler and no second table |
| counterexamples | required-open | **required-open**, and three certificate mutants landed | `mutantSelectedD0`, `mutantAliasedResults` and `mutantFlushOnW0` exist with their three rejection receipts, which is what keeps `sourceCheck = fun _ => true` from satisfying every receipt above them. Their `WS-CONFIG` register rows are still owed, `test/counterexamples/REGISTER.md` being outside the fence, and `WS-PROM-CE-039`'s row is owed at landing. No configuration witness and no scheduler mutant is landed |
| bridges | required-open | **required-open**, and Q4's half of CFG-WPT landed | The whole seam is stated and proved as amendment A5 splits it: the four checkers with their `_iff` ties, the pinned certificate and reference with three non-vacuity receipts, `erasure_preserves_selected_order` on the reference side and `erases_prefix_selected_order` on the target side. The edge stays open on P8's half — `run_erases_to_reference`, the transcription gate, the host replay — and on CFG-LOCAL, CFG-OBS, CFG-HOST and the full component embeddings |
| targets | not-applicable | **not-applicable**, unchanged | This landing generates no target program |
| trust | required-open | **required-open**, and the receipt half delivered | All 93 named receipts print, all inside the R-11 ceiling: 16 with no axioms, 35 `[propext]`, 33 `[propext, Quot.sound]`, 9 `[propext, Classical.choice, Quot.sound]`. `lake exe trustselftest` passes in both directions against an **empty** declared red set, so the all-green control is restored. Independent review is still not done, and that is what the edge is now open on |
| coverage | required-open | **required-open**, unchanged | No coverage state moves. A7 amends the Q1 identity pin to 32012 bytes / `247f9909…a63c` under R-P26, which is a disposition fact, not a coverage fact; the Streams block re-emits byte-identically and all four census standards pass |

**Edges closed at this landing: none. Edges reopened: none.** What the landing
does close is the packet's own delivery list: the 158 restated ascriptions, the
15 Q4-owned receipts, the 38 `PromiseBridgeQ4` ascriptions and the 86 `Source`
ascriptions all elaborate, with no statement changed. The
configuration-breaker hold can be released on that basis; the coordinator owns
that sentence, and the "Q4 landing receipt (second pass)" of
`docs/PROMISE-PACKAGE-PLAN.md` carries it.

## Current-state table as hand-written before the ledger, 2026-10-01

Moved verbatim from the "Current state" section of `docs/CONFIGURATION-DAG.md` at `5999363`; the ledger entry `WhatwgTest/Ledger/ConfigurationOrdering.lean` and its projection `generated/graphs/CONFIGURATION-PG-ORDERING.md` supersede it.

This table describes commit `325d5d5` on 2026-09-30, with the trust and
representation rows brought to the lane V landing of 2026-10-01 (R-V6, R-V8). Its last landing record
is the second Q4 builder pass, and ruling R-P27 accepted that landing after
independent review of `1d400b4`. Ruling R-V4 sets the rule: an edge is
`required-closed` only when every ground this document or a ruling in
`COORDINATION.md` states for keeping it open is discharged by something named
in the ground cell. Where a document and a later ruling disagree, the ruling
wins and the cell names it.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The generated declaration join, which has no generator (debt D47). All 15 class [R] ascriptions elaborate since amendment A1; `phaseErase`, `reactionErase` and the 86 `Source` names are added (Q4 landing, second pass) |
| construction | `required-open` | CFG-START, CFG-CELLS, CFG-TOKENS, CFG-STACK and inductive reachable-state preservation. Debt D38: `notifySettled_eq`'s owner conjunct rests on `CellsWellFormed`, which is not yet stated (CFG-CELLS) |
| semantics | `required-open` | CFG-EFFECTS, CFG-FIFO (its PROCESS/ADVANCE corollary is still owed), CFG-RUNS, the foreign profile, the global scheduler and the live frontiers (Q4 landing, second pass) |
| laws | `required-open` | All 54 restated law ascriptions, the 15 Q4-owned bridging receipts and the 18 deferred-generalization ascriptions are proved. The edge stays open on the obligations §3.3 of the contract lists and no law here states: `WellFormed` initialization and preservation, the successful-profile progress theorem, the ordered-effect receipts, the token/mailbox correspondence and the finite witness through the original start gate (Q4 landing, second pass) |
| representation | `required-open` | Ruled open by R-V8: the second pass keeps the edge open and names no remaining item, so the remaining ground is named here. The landing records report one cell owner, one payload owner, no shadow scheduler, no second table, and the four view record rows of contract §4.1 with their twenty ascriptions; they say nothing of the freeze-time items "typed references" and "no closures". The nearest named open item is in "Required residual embeddings" below: a stable typed address for the P4 read and closed cells, since `E-24` keeps `Readable.State.closedPromise` by value |
| counterexamples | `required-open` | The actual configuration witness, the stable registered scheduler mutants, the retained failing alternatives, and the `WS-CONFIG` register rows of the three certificate mutants `mutantSelectedD0`, `mutantAliasedResults` and `mutantFlushOnW0` (debt D39). `WS-PROM-CE-039` is registered `CLOSED` (R-P27) |
| bridges | `required-open` | The P8 half of CFG-WPT: the existence half `run_erases_to_reference`, the transcription gate to the sealed WPT bytes (debt D35) and the host replay; CFG-LOCAL, CFG-OBS, CFG-HOST and the full P4/P5/P6/P7 embeddings. Debts D34, D36 and D37 are recorded against the CFG-WPT seam |
| targets | `not-applicable` | This graph generates no target program; P11 owns target lowering |
| trust | `required-closed` | The document held the edge open on independent review alone (Q4 landing, second pass); ruling R-P27 records that review of `1d400b4` as done, so the edge closes on R-P27. The 93 named receipts print inside the R-11 ceiling and `lake exe trustselftest` passes against an empty declared red set (Q4 landing, second pass). At `325d5d5` nine receipts reached `Classical.choice`: `readTable_settleReadCell`, `readTable_settleReadCells`, `Transform.settle_table_bridge`, `Transform.settle_waiting_once`, `notifySettled_queued_serial`, `notifySettled_reactions_bridge`, `successfulControl_sink_at_most_one`, `Source.erases_prefix_selected_order` and `Source.erasure_preserves_selected_order`. Slice V5 of lane V repaired all nine with no statement changed and removed the three global `@[simp]` attributes on `freshReadCell`, `settleReadCell` and `settleReadCells` that R-P27 had re-frozen as debt D43; since that landing the axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception (R-V1, R-V6). D43 is closed |
| coverage | `required-open` | The exact clause and numerator joins. The R-P5 re-disposition of `slot.promise-state` and `slot.promise-is-handled` to `owned` moved no coverage state (Q4 landing, second pass) |

The ledger entry of this graph in `WhatwgTest/Ledger.lean` is projected to
`generated/graphs/CONFIGURATION-PG-ORDERING.md` by
`lake exe whatwg_ledger --write`, and `lake exe whatwg_ledger` checks that
projection and the entry's references, not this table.
