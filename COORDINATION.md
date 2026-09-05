# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-05. W0–W5, HTML H0–H4, and the Infra integration repair
at `319e744` are committed. P4a landed at `5121268` and P5a at `e4d053a`.
P6a landed at `afb57f8`; the P7a implementation and verified receipt accompany
this update. The separate configuration breaker is preparing the P8a packet.

## Who is active

| Agent | Working on |
| --- | --- |
| Codex integration coordinator | P7a verified landing on `codex/streams-reification`; coordinating the P8a breadth packet |
| Codex transform breaker | P6a packet and two elaboration annotations frozen at `c420aa9` in `codex/transform-breaker`; verification window released |
| Codex piping breaker | P7a packet frozen at `2f43183`, integrated as `ea03725`; retained ownership of exact statements and witnesses |
| Codex independent reviewer | P7a general/composed proofs and final landing records accepted; P8a draft review continues |
| Codex configuration breaker | Preparing the unfrozen P8a ordering ascriptions, independent source certificate and adversarial battery; no production or Lean work |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| future P8 configuration contract and `docs/CONFIGURATION-DAG.md` design proposal | Codex configuration breaker, 2026-09-05 | Read-only investigation and independently authored proposal in a separate worktree; selects one pinned WPT promise-ordering representative, canonical component/supply seam and exact observation obligations. No production edits or Lean runs before coordinated admission. |
| `test/contracts/piping-shutdown.contract.md`, declaration/source rows in `docs/PIPING-DAG.md`, piping batteries/witnesses and attack descriptions | Codex piping breaker (landed) | Frozen at `2f43183`, integrated as `ea03725`; statements and witnesses remain breaker-owned. All five P7 battery/witness modules are green; coordinator repair/status receipts remain separate. |
| `test/contracts/transform-backpressure.contract.md`, declaration/anchor rows in `docs/TRANSFORM-DAG.md`, `WhatwgTest/Streams/Transform/**`, `WhatwgTest/Streams/Counterexamples/Transform/**`, transform attacks and attacked-statement/witness cells of `WS-TRANS-CE-*` | Codex transform breaker (landed) | P6a packet at `03547f1`, based on `5121268`, with two elaboration annotations at `c420aa9`; statements and witnesses remain breaker-owned. All four P6 batteries/witness modules are green. |
| `test/contracts/writable-default.contract.md`, declaration/statement rows in `docs/WRITABLE-DAG.md`, `WhatwgTest/Streams/Writable/**`, `WhatwgTest/Streams/Counterexamples/Writable/**`, `test/counterexamples/writable/ATTACKS.md` | Codex writable breaker (landed) | Frozen base/lifecycle/exact packets integrated as `5669062`, `47a86da`, `5f7cebe`; statements and witnesses remain breaker-owned. All seven batteries and both witness modules are green. |
| `test/contracts/readable-default.contract.md`, `WhatwgTest/Streams/Readable/**`, declaration/statement rows in `docs/READABLE-DAG.md`, `WhatwgTest/Streams/Counterexamples/Readable/**`, `test/counterexamples/readable/ATTACKS.md` | Codex P4 breaker (landed) | Frozen at `f4394d8`; retained ownership of statements and witnesses. Both batteries are green. Coordinator landing receipts and attack statuses are recorded separately. |
| `test/contracts/queue-with-sizes.contract.md` | P3 breaker (landed) | frozen 2026-09-02; the builder may not edit it |
| `WhatwgTest/Streams/Data/QueueContract.lean`, `WhatwgTest/Streams/Data/QueueAxiomReport.lean` | P3 breaker (landed) | frozen and RED; declared in `test/fixtures/trust-gate/known-red.txt`; the builder may repair elaboration only, never a statement |
| `WhatwgTest/Streams/Counterexamples/Data/Queue.lean`, `test/counterexamples/data/ATTACKS.md`, the `WS-DATA-*` rows of `test/counterexamples/REGISTER.md` | P3 breaker (landed) | green; breaker-owned, retained after the repair |
| `docs/DATA-DAG.md` | P3 breaker (landed) | carries `DATA-PG-QUEUE` and ruling request `P3-R1`; the coordinator answers `P3-R1` there |

Released: the P0 bootstrap claim; the S1.0 seat; the three R0 seats; the S1
one-shot builder (`a8f08d0`); the P1 census seat (`72b1bfd`); the P2 + P1.1
seat (`c2b4497`); the S1.5–S1.7 seat (`a1383bc`); the P3 breaker seat (this
merge). The worktrees `..\lean4-WHATWG-streams-p1`, `-s1`, and `-p3` are
merged and unclaimed.

The former HTML claim released at its committed landings `b163f53`,
`047916b`, and `b4c825a`; the former W0–W5 hold released under the package
plan's executed ledger. The P3 breaker rows above remain frozen ownership
records; their old RED label is superseded by `docs/DATA-DAG.md`'s Landing
receipt and the empty `known-red.txt` set.

The Infra integration, hash-pin repair, and `WS-INFRA-CE-001` claims released
at `319e744`, after the narrow proofs, full build, axiom receipt, executable
gates, and independent review passed.

The P4a implementation, host fixture, and coordinator receipt claims release
with the accompanying implementation commit. The narrow 63-job and full
260-job builds, R-11 audit, executable gates, and independent source/record
reviews passed. `docs/READABLE-DAG.md` owns the exact commands and the open
global/reachability/coverage obligations; full P4 remains open.

The P5a implementation, host fixture, dependency-record cleanup, and coordinator
receipt claims release with the accompanying implementation commit. All nine
narrow modules (72 jobs), the full 275-job build, 111 theorem receipts, root
audit, executable gates, and independent source/record reviews pass.
`docs/WRITABLE-DAG.md` owns exact scope and commands. Full P5 remains open.

The P6a implementation, host fixture, counterexample repair cells and
coordinator receipt claims release with the accompanying implementation
commit. All four narrow modules (71 jobs), the full 287-job build, 118
theorem receipts, root audit, executable gates and independent source/proof
review pass. `docs/TRANSFORM-DAG.md` owns exact commands and the remaining
graph obligations. Full P6 remains open. At that landing the P7a breaker
packet was being prepared in its separate worktree.

The P7a production, root integration, counterexample repair/status and
coordinator receipt claims release with the accompanying implementation
commit. The 75-job narrow build, 298-job full build, all 46 theorem receipts,
149-module/11780-declaration root audit, executable gates and independent
source/proof/landing reviews pass. `docs/PIPING-DAG.md` owns the exact
fragment judgment, commands and open edges. The two composed runs end at
the request to finalize; full P7, progress, global M1/M2 and host embeddings
remain open. The separate P8a packet remains unfrozen and unverified.

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.

## Standing rule while a builder holds the tree

Only the seat that holds a claim on a Lean tree runs `lake` in this checkout.
Research seats measure in scratchpad packages; a second builder works in a
git worktree on its own branch. The coordinator runs the gates only at
landing, after the seat has reported and stopped.
