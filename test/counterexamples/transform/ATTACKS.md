# Transform backpressure attacks

Status: frozen packet; fourteen finite witnesses kernel checked, 2026-09-05. Evidence lives in
`WhatwgTest/Streams/Counterexamples/Transform/Backpressure.lean` under the
`Breaker` namespace. These small independent machines exercise the stated
finite protocol projections. They are not full stream executions or host
observations. They import no production transform declarations.

Each tape below is an actual composition of the named breaker transitions;
an initial raw record is identified explicitly. A production repair must
also satisfy the canonical P4/P5 coupling laws in the transform contract.
Passing these finite probes alone closes neither coupling nor coverage.

| ID | Tape and initial state | Observation / attacked mutation |
| --- | --- | --- |
| `WS-TRANS-CE-001` | `initial; change false` | Cell identity/outcome projection: old ID 4 fulfilled, new ID 5 pending, cursor 6. Reusing or overwriting ID 4 loses identity. |
| `WS-TRANS-CE-002` | `initial; sourcePull` | Returned-ID trace ends at NEW ID 5; mutant returns OLD ID 4. This is the source-pull protocol projection only. |
| `WS-TRANS-CE-003` | `initial; waitWrite; sourcePull` | OLD subscription becomes queued; a retargeted NEW subscription misses that wakeup. |
| `WS-TRANS-CE-004` | `initial; waitWrite; sourcePull` | Sink result remains pending and only the continuation is queued; mutant directly fulfills the sink on unblock. |
| `WS-TRANS-CE-005` | `initial; waitWrite; writable := erroring 17; sourcePull; runWriteReaction` | Explicit intervening error-state transition; reference rejects sink with 17, mutant invokes transform without rechecking. Finite status/continuation projection. |
| `WS-TRANS-CE-006` | `enterCallback; answer` versus `enterCallback; returnPending; answer` | First answer inadmissible, second queues the reaction. This distinguishes synchronous return from eventual settlement. |
| `WS-TRANS-CE-007` | `enterCallback; returnSettled` | Synchronous return precedes reaction attachment; mutant swaps the two events. Local registration-order projection supporting later M2 embedding. |
| `WS-TRANS-CE-008` | `enterCallback` with an already queued reaction; `runCallbackJob` | Live callback blocks the job; after `returnSettled`, the same job may settle. The queued initial case is explicitly a raw protocol state, not a claimed reachable full stream. |
| `WS-TRANS-CE-009` | `outputInitial; outputRead; outputEnqueue 31` | Count-size demand: pending read at HWM zero removes pressure, delivery consumes demand and raises pressure. Size-only mutant misses the pending read. Delivered chunk is an M1 component. |
| `WS-TRANS-CE-010` | `outputInitial; outputEnqueue 29; outputTerminate; outputRead` | Queued chunk survives termination; close precedes the final chunk settlement in this attached-reader projection. Queue-dropping mutant loses an M1 chunk. |
| `WS-TRANS-CE-011` | `outputInitial; outputEnqueue 12; outputEnqueue 34; outputRead; outputRead` | Two outputs delivered FIFO; no enqueue is also a legal empty output trace. This fixes zero/multiple outputs without modeling the foreign transform body. |
| `WS-TRANS-CE-012` | `initial; waitWrite; sourcePull` | The exact trace queues the old subscriber when resolving ID 4, before allocating ID 5. Independent review found and corrected the original fixture's swapped administrative event order. |
| `WS-TRANS-CE-013` | `enterCallback` in an owner with algorithms; `clearOwner; returnOwner` | The active callback can still return after installed algorithms are cleared; a mutant that rechecks algorithm availability loses that continuation. |
| `WS-TRANS-CE-014` | `initial` with output capacity one; `successfulReadableStart; beginProjectedWrite` | Successful readable start services native pull before the next writer call. The bare-start mutant keeps initial pressure and stalls despite capacity. |

The production mask is not established by these independent local traces.
Their roles are to separate concrete mutant choices and force the frozen
general adapter/transition statements. Host and global DB-04 relations remain
open.

Verification used pinned Lean 4.33.1, `LEAN_NUM_THREADS=1`, and the verified
P4 artifacts at coordinator commit `5121268d3c148678bfbe501b245881631524f2e5`:

```powershell
$env:LEAN_PATH = 'C:/Users/kokok/Dev/lean4-WHATWG-streams/.lake/build/lib/lean'
lean -M2048 WhatwgTest/Streams/Counterexamples/Transform/Backpressure.lean
```

The initial eleven-witness command exited 0 in 1.18 seconds. Independent
review then corrected the waiter-case event order in `change`: resolution
queues an old subscriber before the new cell is allocated. CE-012 retains
that corrected sequence; CE-013 retains the active-return/cleared-algorithm
distinction. The thirteen-witness command exited 0 in 1.15 seconds. Twelve
receipts are axiom-free; CE-005 reaches only `propext`. No full build was run
in this worktree. A later source review found that positive readable capacity
must execute the successful-start demand tail before exposing a writer
frontier. CE-014 retains this correction; the fourteen-witness check passed
with twelve axiom-free receipts and `propext` for CE-005 and CE-014. The exact
immutable packet commit is supplied in the freeze handoff.
