# P7a forward-error shutdown representative

Status: **frozen independent breaker packet, 2026-09-05**. Builder admission
is limited to this exact representative and its unchanged tests.
Base: `5d95212e5b3953ec58616b7a0c7493627fa7fcfe` in the separate
`codex/piping-breaker` worktree. `docs/PIPING-DAG.md` owns the proposed
declaration roles, source anchors, assurance route, and residual map.

## Purpose and boundary

The piping requirements are a predicate over runs. The pinned reference
`ReadableStreamPipeTo` is one candidate realizer; its control flow does not
define that predicate. This first representative isolates **forward source
error, write draining, and the optional destination abort action** after
intrinsic reader/writer acquisition and successful component setup.

The exact entry is a quiescent, already-delivered readable batch and a fresh
canonical writable view. Each read ID/chunk comes from the actual P4
settlement trace; all links initially remain unwritten. Source may be
readable or errored. Before error, the candidate submits the batch subject
to canonical desired size; after error, it latches and drains the remaining
already-read chunks. It performs no additional reads. The two composed
obligations provide actual P4 enqueue/read prefixes followed by P5 writes.
Arbitrary entry checkpoints with earlier writer activity require an
additional history/embedding obligation; they are not admitted by claiming
unverified existing write links.

The endpoint is a request to finalize with an exact reason. It is not a
settled pipe promise, released lock, completed pipe, or the full DB-04 M1.
P4 and P5 currently model fixed attached reader/writer lifecycles. Their
canonical cancellation and release operations do not exist yet. Those
operations are owned/open, not foreign bodies or refusals. This packet may
only claim a named shutdown-fragment observation and a corresponding
requirements theorem. P7's full realizability theorem remains open.

No signal is installed in this profile. `preventAbort` is a Boolean already
converted at the API boundary. `preventClose` and `preventCancel` have no
effect on this selected forward-error rule; their other branches remain
owned/open. Source error is detected before selecting an alternative
propagation cause. Later competing shutdown requests cannot replace the
latched original reason or start another action.

## Canonical seam

The state embeds actual `Readable.State α ε` and `Writable.State α ε`.
There is no piping copy of a queue, stream status, error carrier, promise
outcome, allocator, or component callback frame. The shared reason is
`Boundary.Exception ε`; canonical identities survive every projection.
P3 sizes and size answers and P4/P5 typed callback returns and settlements
remain unchanged.

Piping owns only its protocol bookkeeping: a shutdown phase, the original
reason, `preventAbort`, the destination guard captured when shutdown is
entered, read/write links, the abort-call/result identity, and its protocol
trace. A read/write link records a P4 read ID and chunk and optionally the
P5 write-promise ID. It does not store another copy of that promise's state.
The link must be justified by actual canonical read settlement and intrinsic
write invocation/return. A chunk remains captured while a size or sink
callback suspends its corresponding write. The entry requires no source
frames, pending read requests, pending pull answer, or source jobs; a P4
captured read continuation cannot be discarded to manufacture this entry.
Integrating such a live continuation across shutdown remains owned/open.

P5 owns all writable allocations and outcomes. Initial writable error supply
is the source's existing `nextError`; this fragment adds no source allocation
or piping allocator. Cross-view global freshness remains an embedding
obligation. Abort is executed using the
actual P5 intrinsic abort decision and deterministic control stages. A
foreign sink abort answer cannot stand in for that whole algorithm. Its
synchronous callback return is distinct from eventual promise settlement;
the P5 signal callback entered by `WritableStreamAbort` remains reentrant
even though this pipe itself has no signal. Already-settled results are
observed only after the caller has obtained and attached to the result.

Canonical P4/P5 jobs are not exposed as choices on the external tape. The
candidate must name its local deterministic integration order and foreign
call frontiers, with no job execution while an enclosing synchronous call
is live. A full ECMAScript/global scheduler relation is an explicit graph
obligation. P6's transform-specific subscription queue is not a generic
runtime to copy. A transform endpoint must be related to the frozen actual
P6 component embedding before a pipe-through claim can be made.

## Independent requirements fragment

`ForwardShutdownSpec` inspects a protocol observation, not a candidate
`Step` proof. `Snapshot` reuses canonical source/destination states as
read-only before/after evidence; it has no candidate control phase. The
record rules require exact intrinsic calls or canonical P4/P5 steps,
read-inventory linkage, and source `nextRead` preservation. Thus the
no-new-read mutant is rejected through a changed canonical `nextRead`, not
recognition of an invented read-attempt event. These historical snapshots
are observation data, not a second active state or promise runtime.

Its clauses are independently stated:

1. The first forward shutdown latches the exact source error and the entry
   destination guard; subsequent requests leave that selection unchanged.
2. After latching, no intrinsic read begins. An intrinsic write can only
   consume a chunk already obtained by an earlier intrinsic read. Each
   admitted read/write link is used at most once and retains chunk order.
3. If destination was writable and not closing at shutdown entry, every
   read chunk is submitted and every corresponding write promise settles
   before the shutdown continuation is invoked. Rejection counts as
   settlement; this is not a wait-for-success requirement. New writes of
   already-read chunks remain in the wait set; a captured stale final-write
   identity cannot release the wait early.
4. If that entry guard is false, shutdown bypasses this drain requirement.
   A later destination-state change cannot retroactively select a different
   entry branch.
5. With `preventAbort`, there is no destination-abort invocation and the
   finalization request retains the source error after any required drain.
   Otherwise exactly one intrinsic destination abort uses that same reason.
6. Finalization is requested only after the abort result settles. Abort
   fulfillment retains the original source error; abort rejection replaces
   it with that exact rejection reason. A write rejection alone never
   replaces the selected source error. An unanswered write/abort remains a
   live frontier and does not synthesize an error or refusal.

The candidate proof must derive these clauses from exact transition laws
and canonical component embeddings. Defining the specification as candidate
reachability, accepting arbitrary callback outcomes for an intrinsic abort,
or proving only a record constructor equation does not meet this contract.

## Intended composed obligations and attacks

The first run should include an actual P4 queued read, an actual P5 write
whose sink result remains pending, a source error, and delayed shutdown.
After the write settles, the actual P5 abort lifecycle either preserves the
source error or produces a distinct action error. Chunks and reasons are
quantified. This is a finite operational shape, not a global termination
claim. A second shape must retain two outstanding write links so that a
single stale wait target cannot satisfy the all-read-chunks requirement.

Retained mutants distinguish: early abort with pending write;
waiting only for fulfillment; forgetting the second write; starting a new
read after shutdown; dropping an already-read chunk; repeating shutdown;
ignoring `preventAbort`; preserving original reason after failed action;
replacing original reason after successful action; reevaluating the entry
guard; conflating sink return with settlement; and claiming finalization
before canonical releases exist. `WS-PIPE-CE-001` through `016` have exact
finite witnesses and named production-law links in the central register.
The finalization limit is a scope obligation; no numerical fixture claims
that missing canonical releases have happened.

## Evidence and freeze conditions

The sealed Streams text is the semantic owner. The reference implementation
was read as second-tier evidence, including its `currentWrite` identity
recheck in `waitForWritesToFinish`. Pinned WPT forward-error tests include
pending final-write, `preventAbort`, action-rejection, and two-write drain
cases. They have been read, not executed. No host observation is used to
repair a statement.

The frozen packet contains 98 interface ascriptions, 44 exact stage and
requirements laws, two quantified composed laws, and 46 theorem receipts.
Independent review settled the exact protocol trace shape, canonical
read/write-link admission, deterministic local scheduling, and finalization
boundary. The breaker freezes exact interface/law ascriptions, retained
witnesses, axiom receipt names, anchor hashes and red receipts.
Coordinator integration owns roots and known-red
entries. All final direct checks are terminal; exact hashes and classified
receipts follow.

## Verification and immutable-surface ledger

The exact independent surface has 98 interface checks, 44 requirements and
candidate laws, two quantified composed laws, and 46 production theorem
receipt names. Sixteen independent finite witnesses passed. Only their
finite judgments are green; the production declarations and bridge remain
absent at the red checkpoint.

The breaker base is `5d95212e5b3953ec58616b7a0c7493627fa7fcfe`.
Commands ran sequentially from the separate piping worktree under pinned
Lean 4.33.1, using verified main artifacts at
`afb57f8ee0d889b1b4866138e31862e0cf825fd4`. The imported P4/P5 production
surface is unchanged by this packet. No P6 mutable signature, stub
implementation, or temporary production declaration was introduced.

```powershell
$env:LEAN_NUM_THREADS='1'
$env:LEAN_PATH='C:\Users\kokok\Dev\lean4-WHATWG-streams\.lake\build\lib\lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Counterexamples/Piping/Shutdown.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Piping/ShutdownContract.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Piping/ShutdownLaws.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Piping/ShutdownRuns.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Piping/ShutdownAxiomReport.lean
```

| File | Actual Lean exit | Classified result | Final source SHA-256 |
| --- | --- | --- | --- |
| `Counterexamples/Piping/Shutdown.lean` | 0 | 16 finite witnesses; R-11 ceiling, exact axiom split in attack receipt | `46e2d65951bc18cda10be3f0b21d41dd722b670758179160fe2b3a7663056701` |
| `Piping/ShutdownContract.lean` | 1 | 236 unknown production identifiers | `b82ba5b9dca1ac3a609c62e0c6a8db74e2e7ba0f0c625e53b49e6bb0aa588c8e` |
| `Piping/ShutdownLaws.lean` | 1 | 187 unknown identifiers; 13 constructor, 8 field, 3 expected-type, 2 record cascades | `66f21e96373c3808df1c9ea1b306b650dc421abb15e9588f804753264215e1b3` |
| `Piping/ShutdownRuns.lean` | 1 | 27 unknown identifiers; 10 constructor and 7 expected-type cascades | `d5f412f1446d82ab8eb754234d40a2b26a405565bd7a75400a363385bfba356b` |
| `Piping/ShutdownAxiomReport.lean` | 1 | 46 unknown production constants | `b8b29b285ec3a466acb5db0c6cfdfe8ce1658fd1df6aa565619d954ddc88e339` |

Paths in the table are below `WhatwgTest/Streams/`. The cascades follow
missing planned types; two record diagnostics mention the elaborator's
error-recovery `sorryAx` term. They are not accepted proof axioms. There is
no residual parser, import, toolchain, or memory failure in these final
outputs. Earlier draft record-layout errors were corrected before this
final run; they do not supply intended-red evidence.

Final logs are in `C:/Users/kokok/AppData/Local/Temp/`:

| Log | SHA-256 |
| --- | --- |
| `whatwg-p7-witness.log` | `96404a1968f60aaf806d980c60aed01448c22210271bbc78f81e1087d389f7b6` |
| `whatwg-p7-ShutdownContract.log` | `a48cff9697efabccb2f4af433ad3e82315959315f846ad083070d0228e40ab51` |
| `whatwg-p7-ShutdownLaws.log` | `5d6fcfa69913d7ae5c7e5a6ecc7fbf0b030cd460ca2091dcfd1ee08dd0641e4c` |
| `whatwg-p7-ShutdownRuns.log` | `b3349efe59854110bbc4558b5f0a4381ea56fbc667802dfa7d42ed33a14e3740` |
| `whatwg-p7-ShutdownAxiomReport.log` | `49c00206d64dc943443d4898ba79ca3c82de1ef0d95dc28b710f8aef8f9aeb4c` |

The coordinator registers exactly the four `WhatwgTest.Streams.Piping.*`
red modules above in `known-red.txt` when integrating, then removes them
when their unchanged batteries turn green. This separate packet changes no
production, root import, Lake configuration, known-red file, or vendor
bytes. Its `COORDINATION.md` claim is local and omitted from the commit.
Full build, root axiom gate, executable gates, proof-graph closure and
independent implementation review remain builder/coordinator obligations.

## Independent freeze acceptance

The independent reviewer read the 98 interface entries, 44 exact laws and
both canonical tape shapes; no semantic contradiction remained. The reviewer
independently rehashed all eight primary-source spans, joined the 46 theorem
names to their ascriptions and receipts, checked every final source and log
digest, and classified every red diagnostic as a planned missing Piping
name or its elaboration cascade. CE-015 and CE-016 close the requested
post-latch owed-write and no-new-read retained-witness gaps. Final witness
receipts are eight axiom-free, three `propext`, and five
`propext`/`Quot.sound`. The review was read-only; Lean commands were run by
the breaker in coordinator-granted windows.

This commit freezes exactly the contract, `docs/PIPING-DAG.md`, the four
`WhatwgTest/Streams/Piping/Shutdown*.lean` files, the independent
`WhatwgTest/Streams/Counterexamples/Piping/Shutdown.lean` witness file,
the piping attack file, and new `WS-PIPE-CE-*` register rows. The remaining
proof edges and full P7 obligations in the DAG remain required-open.
