# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-02 (reorganization in progress: this repository becomes the single `whatwg` package per `docs/WHATWG-PACKAGE-PLAN.md`; lean4-hash finished at `0168306`; no other seat runs `lake` here until W3 lands).

## Who is active

| Agent | Working on |
| --- | --- |
| Claude (coordinator) | reviews, commits, rulings, routers, PLAN, SPEC-MANIFEST, docs/*.md |
| Claude (operator session, Mac) | `docs/WHATWG-PACKAGE-PLAN.md` slices W0–W5: the whole tree during the rename and the hash/effects requires; claims released per slice in the plan ledger |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| `test/contracts/infra-scalar-constructive.contract.md`, `WhatwgTest/Infra/ScalarConstructiveContract.lean`, `test/fixtures/trust-gate/known-red.txt` | Codex (Infra scalar constructive breaker, 2026-09-05) | freezes all nine existing signatures and the `[propext, Quot.sound]` transitive axiom ceiling for `INFRA-SCALAR-CE-001`; exclusive one narrow red build, then returns Lake to root |
| `Whatwg/Url.lean`, `Whatwg/Url/**`, `Gates/Census.lean`, future URL census tooling and `census/url/**`, `generated/url-census.tsv`, `WhatwgTest/Audit/Url/**`, `docs/URL-PACKAGE-PLAN.md` | Codex (URL reification coordinator, Windows, 2026-09-05) | isolated `dbbf` worktree, branch `codex/url-reification`, base `c1c7caa`; U0/U1 and U2a verified, U2 semantic census next; owns Lake runs here; full reification goal active |
| `test/contracts/queue-with-sizes.contract.md` | P3 breaker (landed) | frozen 2026-09-02; the builder may not edit it |
| `WhatwgTest/Streams/Data/QueueContract.lean`, `WhatwgTest/Streams/Data/QueueAxiomReport.lean` | P3 breaker (landed) | frozen and RED; declared in `test/fixtures/trust-gate/known-red.txt`; the builder may repair elaboration only, never a statement |
| `WhatwgTest/Streams/Counterexamples/Data/Queue.lean`, `test/counterexamples/data/ATTACKS.md`, the `WS-DATA-*` rows of `test/counterexamples/REGISTER.md` | P3 breaker (landed) | green; breaker-owned, retained after the repair |
| `Whatwg/Html.lean`, `Whatwg/Html/**`, `Gates/TyxmlSchema.lean`, `bin/TyxmlSchema.lean`, `generated/tyxml-html-schema.tsv`, `vendor/tyxml-d2916535/`, `vendor/whatwg-html-746f2ede/`, `docs/HTML-PACKAGE-PLAN.md` | Claude (HTML port seat, Mac, 2026-09-03) | H0–H2 landed in the working tree, uncommitted (H2: `Gates/TyxmlSchemaEmit.lean`, the generated `Whatwg/Html/Schema/*.lean`, `WhatwgTest/Html/DecideBenchmark.lean`, and the parity receipt scoped to exclude `Whatwg.Html`); released at commit |
| `docs/DATA-DAG.md` | P3 breaker (landed) | carries `DATA-PG-QUEUE` and ruling request `P3-R1`; the coordinator answers `P3-R1` there |

Released: the P0 bootstrap claim; the S1.0 seat; the three R0 seats; the S1
one-shot builder (`a8f08d0`); the P1 census seat (`72b1bfd`); the P2 + P1.1
seat (`c2b4497`); the S1.5–S1.7 seat (`a1383bc`); the P3 breaker seat (this
merge). The worktrees `..\lean4-WHATWG-streams-p1`, `-s1`, and `-p3` are
merged and unclaimed.

URL setup handoff (isolated `dbbf`, 2026-09-05): baseline repair and pinning claims released. The builder landing on `codex/url-reification` includes these changes; `git status` attributes any later work. `docs/URL-PACKAGE-PLAN.md` records files, commands, receipts, and the next census obligations. `INFRA-TEXT-CE-001` is closed; its three independently authored theorem statements in `WhatwgTest/Infra/Counterexamples/CommaSplit.lean` remain frozen. No agent or Lake subprocess from this handoff is left running.

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.

## Standing rule while a builder holds the tree

Only the seat that holds a claim on a Lean tree runs `lake` in this checkout.
Research seats measure in scratchpad packages; a second builder works in a
git worktree on its own branch. The coordinator runs the gates only at
landing, after the seat has reported and stopped.

URL U2a handoff (2026-09-05): scanner, interface, projection, test integration, registry and graph claims released. Breaker packets at afcd91d, 4e4e880, 6db5ec2 and a60add5 remain frozen; all acceptance conditions are unchanged and now pass. The five URL-INV counterexamples are closed as finite tooling regressions. Independent review confirmed all repairs. Default build and all gates pass; the URL plan records commands, actual axiom output and open census edges. No agent or Lake subprocess from U2a remains running. The full URL reification goal and the coordinator's semantic-census claim remain active.

URL U2b handoff (2026-09-05): join implementation, interface, source-review, test/root integration and register claims released. Breaker packets at `6fe8b5c` and `cb4cee5` remain frozen; all 67 original probes and both `URL-CEN-CE-001` refusals pass unchanged. Default build and repository gates pass. Independent review confirms the whitespace repair and the authored source span/explanation corrections. `docs/URL-PACKAGE-PLAN.md` records exact commands, axiom receipts, the constructive dependency baseline and open joins. No reviewer or Lake subprocess from this handoff remains running. The coordinator retains the source-census claim; full reification and the added choice-minimization objective remain active.
