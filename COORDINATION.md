# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-05. W0–W5 and HTML H0–H4 are committed. Codex holds
the integration build in this checkout; the readable breaker uses its own
worktree and coordinates narrow verification to avoid memory contention.

## Who is active

| Agent | Working on |
| --- | --- |
| Codex integration builder | repairs, gates, and landing evidence on `codex/streams-reification` |
| Codex readable breaker | first P4 packet in the separate `codex/readable-breaker` worktree |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| `Whatwg/Infra/**`, `Whatwg/Infra.lean`, `Gates/Census.lean`, `WhatwgTest/Audit/SpecCoverage.lean`, `WhatwgTest/Audit/Infra/**`, `WhatwgTest/Infra/**`, `WhatwgTest.lean`, `census/infra/**`, the Infra census projections, `lake-manifest.json`, `.github/workflows/ci.yml`, `docs/INFRA-PROOF-PLAN.md`, `docs/SPEC-COVERAGE.md`, `PLAN.md` | Codex integration builder, 2026-09-05 | Reproduce and repair the c1c7caa integration failures on `codex/streams-reification`; owns Lake builds in this checkout. Existing frozen Streams statements remain unchanged. |
| `lakefile.toml` | Codex integration builder, 2026-09-05 | Align the unavailable hash revision with the verified pin already used by the lockfile and provenance. |
| `WhatwgTest/Streams/Counterexamples/Infra/Split.lean`, `test/counterexamples/infra/ATTACKS.md`, the `WS-INFRA-CE-001` register row | Codex integration builder, 2026-09-05 | Retain the independently reviewed refutation of the pre-existing trailing-comma example; the algorithm is unchanged. |
| `test/contracts/readable-default.contract.md`, `WhatwgTest/Streams/Readable/**`, `docs/READABLE-DAG.md`, new `WS-READ-CE-*` counterexample rows, `WhatwgTest/Streams/Counterexamples/Readable/**`, `test/counterexamples/readable/ATTACKS.md` | Codex P4 breaker, 2026-09-05 | Separate worktree; freeze the first default-readable lifecycle packet and red battery before any implementation. |
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

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.

## Standing rule while a builder holds the tree

Only the seat that holds a claim on a Lean tree runs `lake` in this checkout.
Research seats measure in scratchpad packages; a second builder works in a
git worktree on its own branch. The coordinator runs the gates only at
landing, after the seat has reported and stopped.
