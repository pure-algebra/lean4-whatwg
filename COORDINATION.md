# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-05. W0–W5, HTML H0–H4, and the Infra integration repair
at `319e744` are committed. The P4a breaker is frozen at `f4394d8`; its
implementation and verified receipt accompany this update. The writable
breaker uses a separate worktree and coordinates narrow verification windows.

## Who is active

| Agent | Working on |
| --- | --- |
| Codex integration coordinator | P4a landing verified; coordinating the next breadth packet on `codex/streams-reification` |
| Codex writable breaker | first P5 packet in the separate `codex/writable-breaker` worktree |
| Codex independent reviewer | P4a implementation and records accepted; reviewing P5a staged equations |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| future `test/contracts/writable-default.contract.md`, `docs/WRITABLE-DAG.md`, `WhatwgTest/Streams/Writable/**`, `WhatwgTest/Streams/Counterexamples/Writable/**`, writable attack and `WS-WRITE-CE-*` rows | Codex writable breaker, 2026-09-05 | Drafts the P5 breadth representative in its own worktree while main implements the frozen P4a packet. No production writes or concurrent Lake builds. |
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

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.

## Standing rule while a builder holds the tree

Only the seat that holds a claim on a Lean tree runs `lake` in this checkout.
Research seats measure in scratchpad packages; a second builder works in a
git worktree on its own branch. The coordinator runs the gates only at
landing, after the seat has reported and stopped.
