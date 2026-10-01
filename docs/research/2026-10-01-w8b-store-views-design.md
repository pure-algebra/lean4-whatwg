# W8b design: views of the Streams stores into the agent record

Status: design record of the W8b seat of review lane W (rulings R-W4, R-W0,
R-W1, R-W9). It recommends a design and leaves every ruling to the
coordinator. It makes no Model Claim, closes no graph edge, changes no
disposition and moves no coverage row. Base commit:
`fea99fb` (`main`: "Claim: the ledger slice D breaker"). Every prototype
named here was built and run in this seat's scratch directory, outside the
tree, with `lake env lean <file>` from the seat's worktree; nothing was placed
under `Whatwg/` or `WhatwgTest/`. The branch changes this file and one index
row of `docs/research/README.md`.

| Subject | Pin |
| --- | --- |
| this repository | `main` at `fea99fb` |
| lean4-effect4 | `refactor/phase1-phase3` at `38686e44` (read only; the lane last read it at `b9d0d19f`, an ancestor 31 commits back) |
| `effects` | `a4ee7a14` (v0.8.0), unchanged in both repositories |
| toolchain | `leanprover/lean4:v4.33.1` |
| addendum Q5b | read at `a6e2ddb` (`test/contracts/promise-agent-q5.contract.md`, section "Addendum Q5b"); its names are treated as available, its code is not on this base |

Evidence labels: `[C]` measured by this seat, with the command; `[S]` read in
source by this seat; `[P]` proved in scratch against the built libraries, with
`Lean.collectAxioms` over every constant the file adds; `[E]` evaluated in
scratch on concrete instances (`#eval`, scratch only); `[H]` not checked.
Masks are DB-04's, written "DB-04 M1" and "DB-04 M2"; the rule for this layer
is the one `Whatwg/Ecma262/Agent.lean` states: an equation whose right side
moves the queue or the settlement trace is DB-04 M2, every other one DB-04 M1.

## 1. Recommendation

1. A view is a **total function** from a calculus state into
   `Agent.Agent value reason body` for the three calculi that allocate every
   promise they give an identity to: `Writable`, `Readable` and the Q4
   configuration. Each
   view fills all nine fields from existing fields and changes none. A lens
   pair is not available: no `update` makes a Streams state a lens target for
   the agent, which `interpret_handlerAt` needs (`[P]`, `wView_no_lens`).
2. **Two value types** map to one table through a tagged sum,
   `CellValue α := unit | read (ReadResult α)`, used where both kinds coexist
   (the readable: its closed promise holds `undefined`, its reads hold read
   results). The writable and the configuration keep `value := Unit`. The
   reason type is already shared, `Boundary.Exception ε`. `WF` and `Minted`
   do not look at values; Q5b's `Coherent` compares them only by equality.
3. **Independent cursors** map to the one cursor by a fixed layout *inside one
   owner*: the writable's identities are the agent's, and the readable's
   closed promise is agent identity `0` with read `k` at `k + 1` and one
   cursor `nextRead + 1`. That is the stable typed address `E-24` lacked, for
   one reader. *Across owners* (the readable and writable halves of a
   transform or a pipe) no function view exists: two allocators that commute
   on the state cannot both allocate at one cursor (`[P]`,
   `no_address_function`), and fixed disjoint ranges are one instance of
   that. Composites need the allocation order as data, a relation over an
   allocation log, which is P8's global configuration.
4. **Jobs.** The Readable and Writable job lists hold reactions to promises
   those calculi never give an identity (the pull and sink results), and they
   forget those promises once the job runs; the configuration's start and
   sink tokens are the same kind. A function view cannot keep a forgotten
   cell, so those queues stay outside the store views and go with the
   composite relation to P8, together with the transform's coupled queue,
   whose subscriptions have positional identities. The one exception is the
   configuration's observer tokens, which react to promises of its own table:
   the configuration view puts them in the agent's queue at their
   registration identity, with no job-serial supply and no phase erasure.
5. **Bridges.** Per store operation, a commuting square with the agent
   operation or the face program on the right (`[P]` for the writable's four
   and the readable's two). Per calculus step, one statement
   `agentView t = (Agent.runOps (agentView s) (storeOps s t)).1`, where
   `storeOps` is first-order data computed from the two states: the
   allocations the cursor moved over, the settlements the trace gained in
   trace order, the identities newly marked handled and, for the
   configuration, the registrations and the activation change (`[E]` on 83
   writable, 16 readable and 72 configuration steps, every one equal; not
   proved). Once it is proved, `WF`, `Le` and Q5b's `Coherent` carry to every
   view a run reaches, through the agent's own `WF.runOps` and `Le.step`, from
   a view of the initial state that has them (`[H]`).
6. **What the views surface**, each a counterexample row: P4's error path
   omits `ReadableStreamError` step 7 (the closed promise is marked handled);
   Q4's `Ordering.register` omits `PerformPromiseThen` step 12 (the reacted
   promise is marked handled); `Writable.initial` stores the ready promise
   fulfilled with no settlement event, so its view is `WF` but fails Q5b's
   clause 17; `Readable.settleReadCell` is unguarded, so its square needs a
   pending hypothesis; the positional `Transform.reactions` view lowers its
   cursor when a subscription settles; and the frozen `Ordering.reactions`
   view is not the agent's reaction store.
7. **Slices.** A breaker packet with ten counterexample rows; five builder
   slices: the common layer with the writable store view, then the writable
   step bridge and the readable store view in parallel, then the readable
   step bridge, then the configuration view. No frozen ascription, battery,
   field or definition body changes. All new modules sit under
   `Whatwg/Streams/Views/` in `WhatwgStreams` and import
   `Whatwg.Ecma262.AgentLaws`; the face corollary waits for P12.

## 2. Evidence

### 2.1 Setup and measurements

| What | Result | Command |
| --- | --- | --- |
| base build | 479 jobs, exit 0; gate: 279 source files, 19,940 declarations; `Classical.choice` reached by 84 of 13,965 in `Whatwg`; strict ceiling over 6 prefixes, 0 exceptions | `lake build` after copying `.lake` from the main checkout `[C]` |
| frozen ascription blocks under `WhatwgTest/Streams` | 1,469 | `scan_sets.py` (appendix A.8) `[C]` |
| prototype `W8bWritable.lean` | 79 constants under `W8bProto`; axioms reached: `propext`, `Quot.sound`; none reaches `Classical.choice`; 1.6 s wall for the file without the receipt | `lake env lean W8bWritableAxioms.lean` (the file with `import Lean` and the receipt of appendix A.6 appended) `[P]` |
| prototype `W8bReadable.lean` | 58 constants under `W8bRead`; `propext`, `Quot.sound`; none reaches choice; 1.1 s | same, `W8bReadableAxioms.lean` `[P]` |
| prototype `W8bTransform.lean` | 4 constants; `propext` only; 0.9 s | same `[P]` |
| step probe, writable | 4 runs, 83 consecutive step pairs, all equal; operations exercised: 14 allocations, 9 fulfilments, 6 rejections, 3 handled marks | `lake env lean W8bStepProbe.lean` `[E]` |
| step probe, readable | 2 runs, 16 pairs, all equal (7 allocations, 5 fulfilments, 4 rejections, 1 handled mark); without the step-7 handled mark the error step's pair is unequal | same `[E]` |
| step probe, configuration | 3 runs, 72 pairs, all equal (7 allocations, 6 fulfilments, 2 rejections, 10 registrations, 2 handled marks, 7 job starts, 7 job finishes, 6 script entries, 8 script exits; queue length up to 2); without the THEN-step-12 handled bit, and with the frozen `Ordering.reactions` as the agent's reactions, every run has an unequal pair | `lake env lean W8bConfigProbe.lean` `[E]` |
| lean4-effect4 delta | `git diff --stat b9d0d19f 38686e44` over `Adequacy.lean`, `Protocol.lean`, `Program/Stream.lean`, `Machine/Refinement.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` is empty; 8 files under `src/` changed; 377 files under `src/` at both commits | `git -C …/lean4-effect4 diff --stat`, `ls-tree` `[C]` |

Proof style that stayed under the strict ceiling, as measured on the
prototypes `[C]`: `(2 * a == 2 * b) = (a == b)` and `(a + 1 == b + 1) =
(a == b)` by cases on the Boolean with `Nat.eq_of_mul_eq_mul_left` and
`Nat.add_right_cancel`, never `simp` or `omega` (the first versions of
`pick_resolve` and `pick_reject` reached `Classical.choice` through
`by simp` closing `¬ (n == n) = false` and through `omega` under an `≠`
hypothesis); `List.find?_cons_of_pos (p := …)` with an explicit predicate in
place of a bare `simp` (the first `freshPromise_fulfilled_split` reached
choice through one). `Whatwg/AGENTS.md`'s list of traps predicted both.

### 2.2 Inventory (question a)

Every field or structure of the five calculi that is a promise table, a
promise cell, a settlement trace, a reaction or registration list, a job
queue, an activation or a cursor that mints identifiers `[S]`. "Ascription
blocks" counts the frozen `#check (@…)` blocks under `WhatwgTest/Streams`
that name the identifier: each command joined with its indented continuation
lines, `--` and `/- -/` comments stripped, the name matched as a whole
identifier (so `s.readPromises`, `State.readPromises` and `readPromises :=`
match). A name two calculi share (`jobs`, `closedPromise`, `control`,
`active`, `settlementTrace`) is counted once per block whichever calculus it
belongs to `[C]` (`scan_ascriptions.py`, `scan_sets.py`, appendices A.7 and
A.8).

| Calculus | Field or structure | Kind | Value; reason | Minted by | Ecma262 type or parallel | Blocks |
| --- | --- | --- | --- | --- | --- | ---: |
| Readable | `closedPromise : PromiseState Unit ε` | the reader's closed promise, by value, no identity (`E-24`) | `Unit`; `Boundary.Exception ε` | none; set by `streamClose`, `error` | its type **is** `Ecma262.Promise.State` by `abbrev` (`E-01`); held in no table | 13 (shared) |
| Readable | `readPromises : List (Nat × PromiseState (ReadResult α) ε)` | read-promise cells | `ReadResult α`; `Boundary.Exception ε` | `freshReadCell` at `nextRead` | parallel to `Table.entries` with no handled bit; `readTable` is the view (`E-22`) | 18 |
| Readable | `nextRead : Nat` | cursor, from `0` at `initial` | — | `freshReadCell` | parallel to `Table.next` | 11 |
| Readable | `readRequests : List Nat` | pending read identities (`[[readRequests]]`) | — | `read` | Streams slot; no counterpart | 17 |
| Readable | `jobs : List (PullAnswer ε)` | pull reaction jobs | `PullAnswer ε` **is** `Promise.Outcome` by `abbrev` (`E-02`) | `returnPull`, `acceptPullAnswer` | parallel to `Jobs.Queue.pending`; `jobQueue` is the view (`E-48`) | 51 (shared) |
| Readable | `pullAwaiting : Bool` | the foreign pull promise is pending; no identity | — | `returnPull` | Streams slot | 9 |
| Readable | `frames : List (Frame α)` | synchronous activation; `frames = []` is its spelling of `RunCondition` | — | — | Streams slot | 35 |
| Readable | `trace`'s `.settled` events | settlement order; the `closed` entry carries no identity | `Settlement α ε` | every settle site | parallel to `SettlementTrace`; `E-63` keep, bridge deferred | 9 (shared, `settlementTrace`) |
| Writable | `promises : List (Nat × UnitPromise ε)` | cells | `Unit`; `Boundary.Exception ε` | `freshPromise` at `nextPromise` | parallel to `Table.entries`; `promiseTable` is the view (`E-13`..`E-23`) | 8 |
| Writable | `handled : List Nat` | handled set | — | `markHandled` | parallel to the per-cell bit; `promiseTable` folds it (`handled_bridge`) | 6 |
| Writable | `nextPromise : Nat` | cursor, seeded by the caller's `promiseSeed` | — | `freshPromise` | parallel to `Table.next` | 10 |
| Writable | `readyPromise`, `closedPromise : Nat` | references into the table | — | `initial`, `updateBackpressure` | Streams slots | 10, 13 (shared) |
| Writable | `writeRequests : List Nat`; `closeState`, `inFlightWrite`, `abortInFlight`, `pendingAbort` | request references with the phase (`invoking`, `awaiting`, `queued`) of a foreign sink promise that has no identity | — | — | Streams slots | 7 (`writeRequests`) |
| Writable | `jobs : List (SinkJob α ε)` | sink reaction jobs | payload carries `SinkAnswer ε` = `Outcome` by `abbrev` | `attachSink`, `acceptAnswer` | parallel to `Jobs.Queue.pending`; `jobQueue` (`E-45`) | 51 (shared) |
| Writable | `control : List (Control α ε)` | synchronous stack; `.react job` is the running job; `control = []` is its `RunCondition` | — | — | Streams slot | 112 (shared) |
| Writable | `trace`'s `.settled id r` events | settlement order with identities | `settlementTrace s : List (Nat × Except (Boundary.Exception ε) Unit)` **is** `Promise.SettlementTrace Unit (Boundary.Exception ε)` by type | `freshPromise` (born settled), `settle` | `E-71` keep; `settlementTrace_bridge` | 9 (shared) |
| Transform | `backpressurePromise : Nat`, `internalPromises : List Nat`, `pendingTransforms : List (Nat × Nat)` | references into the writable half's table | — | `freshInternal` through `Writable.freshPromise` | Streams slots | 8, 4, — |
| Transform | `subscriptions : List (Subscription α)` | registrations; identities positional | body `Subscription α` | `subscribe` | `reactions` folds `Reactions.add` over it (`E-29`, decision 8) | 8 |
| Transform | `jobs : List (Job α ε)` | the coupled FIFO; component mailboxes in `readable.jobs`, `writable.jobs` | `Job α ε` (`Repr` only) | `notify` | `jobQueue` (`E-52`) | 51 (shared) |
| Transform | `readable`, `writable` | two full component states, two cursors | — | — | the two calculi above | — |
| Piping | `abortPromise : Option Nat`; `links` | references into the destination's table | — | `captureAbort`, `captureWrite` | Streams slots | 11 |
| Piping | `source`, `destination` | two full component states, two cursors | — | — | the two calculi above | — |
| Configuration | `owner : Nat` | the owner of `Promise.Ref` | — | `initial` | `Promise.Ref` is the Ecma262 type | 11 |
| Configuration | `registrations : List (Promise.Reaction Nat)` | reaction records | body `Nat` (callback) | `register` | **is** the Ecma262 record by field type (class [R]); `reactions` is the two-list view | 12 |
| Configuration | `nextObserver : Nat` | registration cursor | — | `register` | parallel to `Reactions.next` | 4 |
| Configuration | `jobs : List Job` | heterogeneous token FIFO (`startup`, `sink`, `observer`) | — | `enqueueJob` | `jobQueue` | 51 (shared) |
| Configuration | `nextJob : Nat` | job-serial cursor, a fourth supply (`WS-PROM-CE-039`) | — | `enqueueJob` | none; `phaseErase` absorbs it | 4 |
| Configuration | `active : Ordering.Active` | activation carrying the whole token | — | `tick`, `decide` | `activeErase` onto `Jobs.Active` | 18 (shared) |

Five frozen `mk` ascriptions fix whole field lists: `Readable.State.mk`,
`Writable.State.mk`, `Transform.State.mk`, `Piping.State.mk` and `Config.mk`
`[C]`. The union of the W8 design's set (the store fields plus
`lookupPromise`, `freshPromise`, `jobQueue`, `promiseTable`, `readTable`) is
167 blocks by this seat's rule; the W8 seat counted 173 by its own joining
rule. Neither number decides anything here, since no field changes. The
existing views name 61 blocks (`readTable` 7, `promiseTable` 13, `jobQueue`
22, `reactions` 13, `activeErase`, `phaseErase`, `reactionErase` 3 each)
`[C]`.

**What already is an Ecma262 type** `[S]`: the carriers, by `abbrev`
(`PromiseState`, `PullAnswer`, `PullReturn`, and on them `UnitPromise`,
`SinkAnswer`, `SinkReturn`); the configuration's `registrations`, by field
type; the writable's settlement trace, by type identity of the list. **What is
parallel storage with a view**: every table (`readPromises`, `promises` with
`handled`), every cursor, every job list, the transform's subscriptions, and
every activation. The only promise in the model with no identity at all is
the reader's closed promise.

### 2.3 The view shapes (question b)

Four shapes were considered.

| Shape | What it needs | Holds for | Fails for |
| --- | --- | --- | --- |
| function `view : State → Agent` | every agent field a function of the calculus state | the writable, the readable, the configuration (2.5, 2.7) | anything with two allocators (2.4) or with promises the state forgets (2.6) |
| relation `Views s a` | a witness the state does not carry (an allocation log, ghost foreign cells) | everything, at the cost of existential witnesses | — |
| lens pair (`view`, `update`), as `handlerAt` wants | `∀ a s, view (update a s) = a` | none of the calculi | every calculus whose view misses some agent: `wView_no_lens` (`[P]`) shows that no `update` exists for the writable, since its view never shows a registered reaction; the readable view has the same witness, and the configuration view needs another one, for example a reaction with no handler (`[H]`) |
| simulation over runs | a relation and a step-matching law | the composite relation of P8 | — |

Decision per calculus:

| Calculus | Shape | Why |
| --- | --- | --- |
| Writable | function `Writable.agentView` | one owner, one cursor, every promise it names is its own; its sink jobs react to foreign promises and stay outside |
| Readable | function `Readable.agentView` | one owner; the closed promise and the reads get a fixed layout; its pull jobs stay outside |
| Configuration | function `Ordering.agentView` | the writable root's store view plus registrations and observer tokens, all on its own table; whether a registration was made before or after its promise settled is read from the configuration's own trace |
| Transform | none in W8b; the two component store views exist | two cursors (2.4) and positional reaction identities (2.8, `WS-VIEW-CE-008`) |
| Piping | none in W8b; the two component store views exist | two cursors |
| composites, and foreign-reaction jobs anywhere | relation over an allocation log, P8 | 2.4 and 2.6 |

lean4-effect4 names the same two shapes at `38686e44`
(`src/Effect4/Laws/Machine/Refinement.lean`, unchanged since `b9d0d19f`)
`[S]`: `Projects project stepC stepM WF`, a function whose image of every
concrete step is one model step with the same operation and the same answer,
and `Refines related stepC stepM`, a relation with lockstep simulation and
frontier matching. Both share one operation alphabet between the two
machines. The views here do not: one Streams step is several agent
operations, which is why the bridge of 2.5 is stated over `Agent.runOps` and
an operation list. A retargeted P12 face that runs the same Streams decision
alphabet on a Streams-over-agent state could take `Projects` as its shape
(2.10).

### 2.4 Two value types and independent cursors (R-W4's question)

**Value types.** Options and their consequences:

| Option | `WF` | `Coherent` (Q5b) | `Minted` | Cost |
| --- | --- | --- | --- | --- |
| tagged sum `CellValue α := unit \| read (ReadResult α)`, one table | value-agnostic: all fourteen clauses read identities and states, never values `[S]` | clauses 17 and 21 compare values by equality, which a sum keeps `[S]` | value-agnostic `[S]` | one inductive with `DecidableEq`, `Repr`; a typing invariant per address kind (the closed cell holds `unit`, reads hold `read _`), which is the Streams counterpart of lean4-effect4's "every value fits its declared type" |
| one agent per table | per agent | per agent | per agent | the readable alone needs two agents, since its closed promise and its reads have different value types; cross-table facts are not statable; two settlement traces with no recorded interleaving |
| core `Sum Unit (ReadResult α)` | as the tagged sum | as the tagged sum | as the tagged sum | no new type, but `Sum.inl ()` reads worse in every statement and still needs an existing-type row as the view's value carrier |
| the writable at `Unit`, the readable at `CellValue α`, composites through an agent value map | as above | as above | as above | recommended: the writable and configuration views keep `(agentView s).table = promiseTable s` by `rfl`, so every landed table bridge applies unchanged; the value map (a generic agent law that `step` commutes with mapping values) is P8's, with the composites |

**Cursors.** Options:

| Option | Allocation squares | `WF` | Note |
| --- | --- | --- | --- |
| identity, one owner (writable, configuration) | hold: `agentView_freshPromise_pending` `[P]` | holds under the cell invariant: `wView_wf` `[P]` | the agent's cursor is `nextPromise`; the function cursor is `2 * nextPromise` |
| fixed layout inside one owner (readable: closed at `0`, read `k` at `k + 1`, cursor `nextRead + 1`) | hold: `rView_freshReadCell_pending` `[P]` | `[H]`, by the same proof shape as the writable | valid because the closed promise is allocated with the reader, before any read; it is the stable typed address `E-24` asks for, for one reader and one generation |
| disjoint ranges by injection (writable `2k`, readable `2k + 1`) | fail: both allocation squares need the one cursor to equal `2 * nextPromise` and `2 * nextRead + 1` at once | holds with the cursor at the maximum `[H]` | an instance of the next row |
| any function view of two commuting allocators | impossible: `no_address_function` and its instance `pair_no_address_function` for a readable/writable pair `[P]` | — | if the view assigns the first allocator's new cell to the cursor, keeps assigned addresses across the second allocator, and advances the cursor on it, the diamond of the two allocations forces the cursor to equal its successor |
| allocation log as data (`ViewsAt (log : List Addr) s a`) | hold, with the log extended by each allocation | transfers through the table agreement | the composite relation; the transform and pipe traces record no event for a pending allocation `[S]`, so the log cannot be recovered from the state and must be ghost data or P8's one cursor |

The answer to R-W4: the two value types become one table through a tagged
sum; the independent cursors become one cursor by a fixed layout inside one
owner and cannot become one cursor by any function across owners, so
cross-owner tables wait for P8's single allocation order.

### 2.5 Bridge theorems (question c)

All theorems below are statements about the views; none is a claim about a
host. Signatures are as elaborated in the prototypes (appendix A), renamed
from `wView`/`rView` to the proposed public names `Writable.agentView` and
`Readable.agentView`.

**The writable store view** `[P]`:

```lean
def Writable.agentView {α ε body : Type} (s : Writable.State α ε) :
    Agent.Agent Unit (Boundary.Exception ε) body :=
  ⟨Writable.promiseTable s, Promise.Reactions.empty, [], Jobs.Queue.empty,
    s.promises.map Views.fnOf, 2 * s.nextPromise, .checkpoint, none,
    Writable.settlementTrace s⟩
```

with `Views.capOf id := ⟨id, 2 * id, 2 * id + 1⟩` and `Views.fnOf (id, st) :=
⟨id, 2 * id, 2 * id + 1, st ≠ pending⟩`: one stored resolving-function record
per cell, fired exactly when the cell is settled. Reactions, held records, the
queue and the activation are those of an agent with no consumer.

| Statement (proved in scratch) | Mask |
| --- | --- |
| `agentView_freshPromise_pending (h : s.nextPromise ∉ s.handled) : agentView (freshPromise s .pending).1 = (Agent.newPromise (agentView s)).1 ∧ (freshPromise s .pending).2 = (Agent.newPromise (agentView s)).2.promise` | DB-04 M1 |
| `agentView_freshPromise_fulfilled (h1 : s.nextPromise ∉ s.handled) (h2 : ∀ p ∈ s.promises, p.1 ≠ s.nextPromise) : agentView (freshPromise s (.fulfilled ())).1 = Agent.resolve (Agent.newPromise (agentView s)).1 (Agent.newPromise (agentView s)).2 ()` | DB-04 M2 |
| `agentView_settle (pick) (hpick : ∀ e, pick (fnOf e) = (e.1 == id)) : agentView (settle s id result) = Agent.callFunctions (agentView s) pick result`, with no other hypothesis: a missing cell has no record, a settled cell's record has fired, a pending cell's record settles it | DB-04 M2 |
| `agentView_settle_ok : agentView (settle s id (.ok ())) = Agent.resolve (agentView s) (capOf id) ()`; `agentView_settle_error`, the same with `Agent.reject` | DB-04 M2 |
| `agentView_markHandled : agentView (markHandled s id) = Agent.markHandled (agentView s) id` | DB-04 M1 |
| `agentView_ensureReadyRejected_pending (h : lookupPromise s s.readyPromise = some .pending) : agentView (ensureReadyRejected s e) = (Agent.runOps (agentView s) [.reject (capOf s.readyPromise) e, .markHandled s.readyPromise]).1` | DB-04 M2 |
| `agentView_wf (hc : CellsFresh s) (ht : TraceCoherent s) : Agent.WF (agentView s)`, all fourteen clauses; `CellsFresh` is identities unique and below the cursor, `TraceCoherent` is no identity settled twice and each recorded settlement the cell's present state | DB-04 M1 |
| `agentView_initial_wf : Agent.WF (agentView (Writable.initial .posInfinity alg0 0 0))` | DB-04 M1 |

The rejected twin of `agentView_freshPromise_fulfilled` follows by the same
two lines from `freshPromise_rejected` `[H]`.

**The readable store view** `[P]`:

```lean
inductive Views.CellValue (α : Type) where
  | unit
  | read (r : Readable.ReadResult α)

def Readable.agentView {α ε body : Type} (s : Readable.State α ε) :
    Agent.Agent (Views.CellValue α) (Boundary.Exception ε) body :=
  ⟨⟨(cells s).map (fun e => (e.1, Promise.Cell.mk e.2 (closedHandled s e.1))), s.nextRead + 1⟩,
    Promise.Reactions.empty, [], Jobs.Queue.empty, (cells s).map Views.fnOf,
    2 * (s.nextRead + 1), .checkpoint, none,
    (Readable.settlementTrace s).map settlementOf⟩
```

where `cells s := (0, closed) :: reads shifted by one`, `closedHandled s 0` is
true exactly when the stream is errored (decision 4), and `settlementOf` sends
`.closed r` to identity `0` and `.read k r` to `k + 1`.

| Statement (proved in scratch) | Mask |
| --- | --- |
| `agentView_freshReadCell_pending : agentView (freshReadCell s .pending).1 = (Agent.newPromise (agentView s)).1 ∧ readAddr (freshReadCell s .pending).2 = (Agent.newPromise (agentView s)).2.promise` | DB-04 M1 |
| `agentView_settleRead_ok (hp : (s.readPromises.find? (·.1 == id)).map Prod.snd = some .pending) : agentView (settleReadTraced s id (.ok x)) = Agent.resolve (agentView s) (capOf (readAddr id)) (.read x)`, where `settleReadTraced` is `settleReadCell` with its trace event, the shape `continuePull` and `beginEnqueue` use | DB-04 M2 |
| `agentView_settlements : (agentView s).settlements = (Readable.settlementTrace s).map settlementOf` (`rfl`): the readable settlement-trace bridge `E-63` deferred because the closed entry had no identity | DB-04 M2 |
| `agentView_closed : Table.get (agentView s).table 0 = some (stateMap (fun _ => .unit) s.closedPromise)` | DB-04 M1 |

**Step-level bridges** (`[E]` on concrete runs, not proved). The operation
list is first-order data computed from the two states:

```lean
def Writable.storeOps {α ε body : Type} (s t : Writable.State α ε) :
    List (Agent.Op Unit (Boundary.Exception ε) body) :=
  List.replicate (t.nextPromise - s.nextPromise) .newPromise ++
    ((Writable.settlementTrace t).drop (Writable.settlementTrace s).length).map settleOp ++
    (t.handled.drop s.handled.length).map .markHandled

theorem Writable.agentView_step {α ε body : Type} {s t : Writable.State α ε}
    {d : Option (Writable.Decision α ε)} :
    Writable.StoreFresh s → Writable.Step s d t →
      Writable.agentView (body := body) t =
        (Agent.runOps (Writable.agentView s) (Writable.storeOps s t)).1
```

`StoreFresh s` is `CellsFresh s` and every handled identity below the cursor
(the hypothesis `freshPromise_bridge` already carries as `nextPromise ∉
handled`). The readable's list adds one `markHandled 0` when the step errors
the stream; the configuration's adds the step's new registrations as
`.perform p (some cb) (some cb) false`, and the activation change as
`startJob`, `finishJob`, `enterScript` or `leaveScript` (appendix A.4, A.5).
All three are DB-04 M2. Allocations are hoisted before the settlements of the
same step; the end agent is the same because allocation commutes with every
store operation on an older cell, which is what the probe measured, and the
claim is about the end agent and the settlement order, not about the order of
operations inside one step.

From the step bridge, with no invariant proof beyond `StoreFresh` (both
`[H]`):

```lean
theorem Writable.reaches_agentView_wf :
    Writable.Reaches (Writable.initial hwm alg seed eSeed) ds t →
      Agent.WF (Writable.agentView (body := body) t)
theorem Writable.step_agentView_le :
    Writable.StoreFresh s → Writable.Step s d t →
      Agent.Le (Writable.agentView (body := body) s) (Writable.agentView t)
```

The first is `agentView_initial_wf` (for each `hwm`), `StoreFresh` kept by
every step, and `Agent.WF.runOps` along `Kernel.Path.lift`; the second is
`Agent.Le.step` folded along the operation list with `Le.trans`. The same
route gives Q5b's `Coherent` from a `Coherent` initial view, which fails at a
positive high-water mark (`WS-VIEW-CE-004`, decision 6).

**Invariant transfer, summarized.** `WF`: to every view reachable from a `WF`
initial view (writable `[P]` at one initial state, step bridge `[E]`).
`Coherent` `[H]` from the clause texts of addendum Q5b: clause 16
(`unfiredPending`) holds of every store view by construction, since a record is
unfired exactly when its cell is pending; clause 15
(`functionPromisesNodup`) follows from `CellsFresh`; clauses 18 to 21 are
vacuous for the writable and readable views (no reaction lists, no held
records, no queue) and hold by construction for the configuration view;
clause 17 needs every settled cell traced, which `Writable.initial` breaks
(`[P]`) and `Ordering.initial`, built on it, breaks the same way `[S]`.
`Minted`: every allocated cell's `capOf` is minted, so `pre` admits `resolve`
and `reject` through it `[S]`.

**Which existing bridge lemmas become corollaries.** None is retired or
re-proved: the new squares are proved *from* `freshPromise_bridge`,
`settle_bridge`, `markHandled_bridge` and `lookupPromise_bridge`, which stay
as the table half. `Writable.settlementTrace_bridge` becomes a statement about
the agent's trace by `rfl` (`(agentView s).settlements = settlementTrace s`).
The readable's `readTable_*` laws stay about the unshifted reads-only view; a
small adapter relates it (`Table.get (agentView s).table (k + 1) =
(Table.get (readTable s) k).map (stateMap .read)`, `[H]`). The job-queue
bridges (`jobQueue_eq`, `tick_dequeue_bridge`, `runPullJob_dequeue_bridge`,
the Transform six) stay: those queues are outside the store views. The Q4
bridges stated modulo an erasure (`notifySettled_reactions_bridge` with
`reactionErase`, `runCondition_iff` with `activeErase`) stay as statements
about Q4's own views; the configuration view's step bridge is their unerased
counterpart at the agent, with the job serial equal to the registration
identity.

### 2.6 Jobs: why the store views leave the Streams queues outside

`[S]` for the mechanism, `[H]` for a witness. The writable's `SinkJob` is the
reaction to the promise a foreign sink algorithm returned; that promise has no
identity in the writable, which records only the request and a phase
(`awaiting`, `queued`), and the in-flight slot is cleared when the job runs.
The readable's pull job reacts to the foreign pull promise (`pullAwaiting`,
no identity). The transform's coupled jobs react to promises of the writable
half's table, but its subscriptions have positional identities (2.8). For the
agent's queue to hold such a job, the agent's table must hold the reacted
promise; a function view could give a foreign promise a cell only while the
calculus remembers it, and drop it after, which `Le.allocated` forbids. So the
store views leave those queues outside, and the one queue for them is the
composite relation's: foreign promises as ghost cells allocated by
`newPromise` at the call, settled by the foreign answer (a decision on the
tape), reacted to by `perform`, which is the shape `CONFIGURATION-PG-ORDERING`'s
"Required residual embeddings" asks for ("a binding between actual pull
invocation and returned promise, and a proof that global token projection
matches `Readable.jobs`").

The configuration's observer tokens are the exception: they react to
promises of the configuration's own table, so its view puts them in the
agent's queue, keyed by registration identity, with the reacted promise's
result as the argument. Start and finish tokens and sink tokens run as host
activations, which the view reads as `Jobs.Active.script` (`enterScript`,
`leaveScript`). The relative order of an observer job and a sink job is
therefore in the configuration's queue and not in the agent's: settlement
order (DB-04 M2's content) is kept, job-start order across kinds is not.

### 2.7 The configuration view (`[E]`, not proved)

The view (appendix A.5) is the writable root's store view extended with:

- reactions: a registration made while its promise was pending is in both
  lists (THEN step 9) with the callback as both handlers, because the
  configuration calls it on either outcome; one made after the promise
  settled is a held record (THEN steps 10 and 11). The trace positions of the
  `registered` event and of the promise's `settled` event decide which. The
  `initial` ready promise, fulfilled with no event, counts as settled before
  every registration;
- phases from the table: `waiting` while pending, then `.queued r.id` on the
  triggered list and `.done` on the other (FULFILL and REJECT steps 4 and 5).
  The configuration's own `queued serial`, `running serial` and `done` are
  not read, so `phaseErase` and `nextJob` have no role in the view;
- the handled bit of a cell is the writable's or set by any registration on
  it (THEN step 12, decision 5);
- the queue: observer tokens, each `⟨registration, result of its promise⟩`;
- the activation: `.observer` of an observer token is `Jobs.Active.job rid`
  with that job running; `.intrinsic` is `script`.

The proposed statement, DB-04 M2 (the prototype's `cView` and `cOps` at
`α ε := Unit`, appendix A.5):

```lean
def Semantics.Ordering.agentOps {α ε : Type} (c t : Config α ε) :
    List (Agent.Op Unit (Boundary.Exception ε) Nat) :=
  Writable.storeOps c.writable t.writable ++
    (t.registrations.drop c.registrations.length).map
      (fun r => .perform r.promise r.handler r.handler false) ++
    activationOps c.active t.active

theorem Semantics.Ordering.agentView_step {α ε : Type} {c t : Config α ε}
    {d : Option (Decision α ε)} :
    Writable.StoreFresh c.writable → RegistrationsFresh c → TokensSettled c →
      Step c d t →
        agentView t = (Agent.runOps (agentView c) (agentOps c t)).1
```

where `activationOps` sends checkpoint to an observer token to `[startJob]`,
back to `[finishJob (.ok ())]` (the reaction carries no capability, so any
decision settles nothing), checkpoint to script or intrinsic to
`[enterScript]` and back to `[leaveScript]`, and `TokensSettled c` says every
observer token names a registration whose promise is settled `[H]`. One step
either registers or settles, never both, so the order of the two middle
blocks is immaterial `[S]`.

Every one of 72 steps of three runs (pre-start observers, writes, a close,
observer returns, script re-entries, a controller error rejecting the closed
promise with two observers queued, and a held registration on the
initially-fulfilled ready promise) satisfies the step bridge `[E]`. Its
`WF` needs, beside the writable's store invariant, `RegistrationsFresh` (W8a's
`Ordering.RegistrationsFresh` gives `heldDistinct`, `reactionsBelow`,
`queueBelow`) and that every observer token names a registration whose promise
is settled `[H]`; or it follows from the step bridge and a `WF` initial view
through `WF.runOps` `[H]`.

### 2.8 What the views surface

| Finding | Evidence | Row |
| --- | --- | --- |
| `Readable.error` rejects the closed promise but never sets its `[[PromiseIsHandled]]`, which `ReadableStreamError` step 7 does: in the sealed `vendor/whatwg-streams-b9ba9f49/index.bs`, the algorithm `readable-stream-error` sets the reader's `[[closedPromise]]`'s `[[PromiseIsHandled]]` to true right after rejecting it | `[S]`; the readable step probe with the bit derived from the status is equal on every step, and without the `markHandled 0` operation the error step is not `[E]` | `WS-VIEW-CE-006` |
| `Ordering.register` (Web IDL "react" at the configuration) never marks the promise handled, which `PerformPromiseThen` step 12 does on every branch (Q3b finding F1, `performPromiseThen_handled`) | `[S]`; with the configuration's handled bits alone every probe run has an unequal step `[E]` | `WS-VIEW-CE-007` |
| `Writable.initial` stores the ready promise fulfilled with no `.settled` event at a positive high-water mark, where `freshPromise` records one for a cell born fulfilled; the view is `WF` there and fails Q5b's clause 17 | `wView_initial_wf`, `wView_initial_not_settledTraced` `[P]` | `WS-VIEW-CE-004` |
| `Readable.settleReadCell` is unguarded (its docstring says so), so the readable settle square needs the pending hypothesis; on a read that has settled, the readable records a second settlement and the agent's `resolve` is inert | `rView_settleRead_unguarded` `[P]` | `WS-VIEW-CE-005` |
| `Transform.reactions` numbers subscriptions by position, so settling one lowers the view's cursor: the view cannot be an agent's reactions under `Le.reactionsNext` | `reactions_cursor_decreases` `[P]` | `WS-VIEW-CE-008` |
| Q4's `Ordering.reactions` gives the reject list no handler and copies the registrations' phases, so a rejection would run no callback and no list is ever cleared; as the configuration view's reactions every probe run has an unequal step | `[S]`, `[E]` | `WS-VIEW-CE-009` |

None of these changes a frozen statement: the views carry the missing bits
(decisions 4 and 5) or the bridges carry the hypothesis, and each departure
becomes a register row.

### 2.9 lean4-effect4 at `38686e44` (a reading)

What follows is a reading of that repository's source at one commit, by this
seat and by one read-only helper seat whose quotations were spot-checked; it
is not a claim about that repository's correctness or intent.

- **Handler adequacy is unchanged since `b9d0d19f`** `[C]`:
  `src/Effect4/Laws/Program/Typed/Adequacy.lean` and
  `src/Effect4/Laws/Effects/Protocol.lean` have no diff. `StoreTyped`,
  `World.leHost`, `StoreCert`, `storePre`, `storePost`, `StoreImplements root
  op` and `storeStep_typed` keep their names and shapes; `storePost` reads the
  answering world only, the earlier world entering through the certificate
  and `w.leHost w'` (debt D66's point). `Protocol.lean` still holds
  `WorldOrder`, `Protocol`, `Typed` and `Protocol.sum`; no `run_adequate`
  exists in a tracked file `[S]` (helper).
- **New since `b9d0d19f`: the typed-state split** `[C]` (`git grep`): in
  `Typed/Assembly.lean`, `MachineTyped root rootTy w m` (the machine-only
  typing) and `ConfigTyped root rootTy w m commands` (with the queue), and
  `storeTyped_of_typedState : MachineTyped root rootTy w m → StoreTyped w`, so
  store typing is now derived from machine typing. Eight files under `src/`
  changed (`Typed/{Assembly,Residual,Scheduler,Sources,State}.lean`,
  `Laws/Machine/{Clauses,StoresLaws,Witnesses}.lean`); none was added or
  removed `[C]`. For a store provider this changes nothing: the shape a
  provider mirrors is still a world order, a typing predicate, `Cert`, `pre`
  and a one-world `post`, and one `*_implements` per operation `[S]`.
- **No stream, channel, sink, queue or scheduler module was added** `[C]`:
  `src/Effect4/Program/Stream.lean` (three external host rows) is unchanged,
  `DeferredStore` still resumes waiters inline (`WakeMode.now`) and posts
  `scheduled` ones to a dispatcher; there is no microtask module `[S]`
  (helper).
- **Decision records** `[S]` (helper): DI-30 (the WHATWG promise and job
  declarations "refused unless reproved") and DI-90 (`Effects.*` in-tree under
  the same names) are unchanged; decisions row 53 (no vendoring) is unchanged
  and open; row 136 gained a "Landed 2026-10-01" note naming store-specific
  adequacy theorems, while its text still promises one generic theorem. No
  successor decision mentions this repository.
- **What a consumer of a store view finds there** `[S]`: `Refinement.Projects`
  and `Refines` (2.3), lockstep over one alphabet; a data `Lens` with
  `Lens.Lawful` in `Data/Optic.lean`, not tied to stores; no `handlerAt`, no
  store view, and no requirement on a consumer's lens.

### 2.10 What the views buy (question d)

**For lean4-effect4.** The face `Whatwg.Signatures.Ecma262` does not serve an
existing Streams calculus through `handlerAt view update`: the lens law fails
for every store view (`wView_no_lens`, `[P]`), and `interpret_handlerAt`
needs it for every agent and state. What the views give a consumer:

1. the agent's laws apply to a Streams store through the view: after a
   writable settle of a pending cell, `post_resolve` (and Q5b's `postFrom`)
   speak of the view, and `Agent.implements` gives `Le` and `WF` for the
   operation the square names;
2. the face's programs read as Streams store behaviour: `run (resolvedWith ())
   (agentView s) = (capOf n, agentView (freshPromise s (.fulfilled ())).1)`
   (`wView_resolvedWith`, `[P]`, DB-04 M2), so a cell the writable allocates
   born fulfilled is the face's "a promise resolved with";
3. the step bridges are the agent half of a P12 adequacy theorem.

A retargeted P12 face then needs, beyond W8b: a Streams-local signature (the
calculus's decision alphabet and the non-promise slots) with its handler; a
Streams-over-agent state `Agent × Local`, on which `handlerAt Prod.fst (fun a
s => (a, s.2))` has its lens law by `rfl`; the calculus step written as a
program over `signature ⊕ₛ Local` whose agent half is `storeOps`; and the
theorem that interpreting that program from `(agentView s, local s)` ends at
`(agentView t, local t)`, which is the `Projects` shape of 2.3 with the
calculus decision alphabet on both sides. The composite calculi (transform,
pipe) need P8's relation first. Effect TS interop stays host evidence (W10's
reading).

**For this repository**, items a view moves; no status changes here:

| Graph, edge | Item | Effect |
| --- | --- | --- |
| `WRITABLE-PG-DEFAULT`, representation and semantics | "ECMAScript promises and reaction registration" | the writable's promise slots become agent promise objects under a named view with squares; reaction registration stays open (no registrations in the writable) |
| `WRITABLE-PG-DEFAULT`, construction | "shared fresh allocation" | `StoreFresh`, kept by every step, is the single-owner half |
| `READABLE-PG-DEFAULT`, representation and semantics | "the promise-object embedding" | moved for the closed and read promises of one reader |
| `CONFIGURATION-PG-ORDERING`, representation | "a stable typed address for the P4 read and closed cells" | moved, not closed: the readable layout is that address for one reader and one generation; the generation view (reader release) and composite addresses stay |
| `CONFIGURATION-PG-ORDERING`, construction | CFG-CELLS | the first two clauses of `CellsWellFormed` (unique identities below the cursor) are `CellsFresh`, a hypothesis of the writable view's `WF` |
| `CONFIGURATION-PG-ORDERING`, laws | "the token/mailbox correspondence" | the observer half: tokens are the agent queue at registration identity |
| `PROMISE-PG-FIRST`, bridges | "`E-63`'s readable settlement-trace bridge" (deferred) | supplied by `Readable.agentView_settlements` and the step bridge |
| `TRANSFORM-PG-BACKPRESSURE`, representation | "promise adoption and registration" | not moved; `WS-VIEW-CE-008` records why the positional view cannot carry it |
| `PROMISE-PG-AGENT`, bridges | — | gains its first Streams consumers; nothing open moves |

## 3. Public declaration record (question f)

Modules, all new, all in the Lake library `WhatwgStreams` under the strict
prefix `Whatwg.Streams`; each imports `Whatwg.Ecma262.AgentLaws` (through it
`Whatwg.Ecma262.Agent`) and the calculus modules it views. The import
direction is `Whatwg.Streams` → `Whatwg.Ecma262`, never the reverse; nothing
here imports `Effects` or `Whatwg.Signatures`. Signatures are as elaborated in
the prototypes under their scratch names; roles follow `Whatwg/AGENTS.md`.
Spec anchors: the store views model `slot.promise-state`,
`slot.promise-is-handled` (the two slots R-P21 re-dispositioned `owned` with
references into `Whatwg.Ecma262`) and the reader's `[[closedPromise]]`; the
step bridges cite the store operations' census rows.

### 3.1 `Whatwg.Streams.Views.Common` (W8b.1)

| Declaration | Signature | Role |
| --- | --- | --- |
| `Views.capOf` | `Nat → Promise.Capability` | helper |
| `Views.fnOf` | `{v r : Type} → Nat × Promise.State v r → Promise.ResolvingFunctions` | helper |
| `Views.stateMap` | `{v w r : Type} → (v → w) → Promise.State v r → Promise.State w r` | helper; no `State.map` exists in `Whatwg.Ecma262.Promise` `[C]` (grep), and its natural owner is there (decision 11) |
| `Views.CellValue` | `Type → Type`, constructors `unit`, `read (r : Readable.ReadResult α)`, `DecidableEq`, `Repr` | view carrier (decision 2) |
| `Views.Addr` | `Type`, constructors `readClosed`, `read (k : Nat)`, `writable (k : Nat)`, `DecidableEq`, `Repr` | canonical typed address; used by the impossibility theorem now and by P8's log |
| `Views.two_mul_beq`, `Views.succ_beq` | `(a b : Nat) → (2 * a == 2 * b) = (a == b)`; `(a + 1 == b + 1) = (a == b)` | helpers (choice-free forms) |
| `Views.find_fnOf`, `Views.mark_fnOf` | the two list laws of `W8bWritable.lean` | helpers |
| `Views.no_address_function` | `{S A : Type} (s : S) (next : S → Nat) (allocW allocR : S → S) (newW : S → A) (addr : S → A → Option Nat) → allocW (allocR s) = allocR (allocW s) → next (allocR s) = next s + 1 → (∀ t, addr (allocW t) (newW t) = some (next t)) → (∀ t x, (addr t x).isSome = true → addr (allocR t) x = addr t x) → newW (allocR s) = newW s → False` | derived; no mask (a fact about addresses) |
| `Views.pair_no_address_function` | its instance at `Readable.State α ε × Writable.State α ε` with `freshReadCell` and `freshPromise` | derived |

### 3.2 `Whatwg.Streams.Views.Writable` (W8b.1)

| Declaration | Signature (shortened by `open`) | Role | Mask |
| --- | --- | --- | --- |
| `Writable.agentView` | `{α ε body : Type} → Writable.State α ε → Agent.Agent Unit (Boundary.Exception ε) body` | view | — |
| `Writable.agentView_table` | `(agentView s).table = promiseTable s` | view law (`rfl`) | M1 |
| `Writable.agentView_settlements` | `(agentView s).settlements = settlementTrace s` | view law (`rfl`) | M2 |
| `Writable.agentView_freshPromise_pending` | 2.5 | adapter | M1 |
| `Writable.agentView_freshPromise_fulfilled`, `_rejected` | 2.5 | adapter | M2 |
| `Writable.agentView_settle`, `_settle_ok`, `_settle_error` | 2.5 | adapter | M2 |
| `Writable.agentView_markHandled` | 2.5 | adapter | M1 |
| `Writable.agentView_ensureReadyRejected_pending` | 2.5 | adapter | M2 |
| `Writable.CellsFresh`, `Writable.TraceCoherent` | `Writable.State α ε → Prop` | invariant | — |
| `Writable.agentView_wf` | `CellsFresh s → TraceCoherent s → Agent.WF (agentView s)` | derived | M1 |
| `Writable.agentView_initial_wf` | `Agent.WF (agentView (initial hwm alg seed eSeed))` for every `hwm`, generalizing the prototype's one instance | derived | M1 |

### 3.3 `Whatwg.Streams.Views.WritableStep` (W8b.2)

| Declaration | Signature | Role | Mask |
| --- | --- | --- | --- |
| `Writable.storeOps` | `Writable.State α ε → Writable.State α ε → List (Agent.Op Unit (Boundary.Exception ε) body)` | view (first-order data) | — |
| `Writable.StoreFresh` | `Writable.State α ε → Prop` | invariant | — |
| `Writable.initial_storeFresh`, `Writable.tick_storeFresh`, `Writable.decide_storeFresh`, `Writable.step_storeFresh` | the four W8a shapes of `QueueInv` | derived | M1 |
| `Writable.agentView_tick`, `Writable.agentView_decide`, `Writable.agentView_step` | 2.5 | derived | M2 |
| `Writable.reaches_agentView_wf`, `Writable.step_agentView_le` | 2.5 | derived | M1, M2 |

### 3.4 `Whatwg.Streams.Views.Readable` and `ReadableStep` (W8b.3, W8b.4)

As 3.2 and 3.3, at `value := Views.CellValue α`, with `Readable.readAddr`,
`Readable.closedHandled`, `Readable.settlementOf`,
`Readable.agentView_closed`, `Readable.agentView_freshReadCell_pending` and
its two settled twins, `Readable.agentView_settleRead_ok` and `_error` (with
the pending hypothesis), `Readable.agentView_streamClose` and
`Readable.agentView_error` (the operation lists `[resolve cap0 .unit] ++
reads` and `[reject cap0 e, markHandled 0] ++ reads`, `[H]`),
`Readable.CellsFresh`, `Readable.agentView_wf`, `Readable.storeOps`,
`Readable.agentView_step`, and the adapter to `readTable`.

### 3.5 `Whatwg.Streams.Views.Configuration` (W8b.5)

`Semantics.Ordering.agentView : Config α ε → Agent.Agent Unit
(Boundary.Exception ε) Nat` (view), with `listedBefore`, `phaseAt`,
`observerJob` (helpers), `Ordering.agentOps` (view, first-order),
`Ordering.agentView_step` (derived, M2), `Ordering.agentView_initial_wf`
and `Ordering.reaches_agentView_wf` (derived, M1).

### 3.6 Duplicate prevention

No declaration of `Init`, `Whatwg` or `effects` maps a Streams state to an
agent `[C]` (grep for `Agent.Agent` outside `Whatwg/Ecma262`, `Whatwg/WebIdl`
and `Whatwg/Signatures`: none). The landed views (`readTable`,
`promiseTable`, `jobQueue`, `reactions`, `activeErase`) are kept and cited as
the components; `Writable.agentView`'s table **is** `promiseTable`.
`storeOps` duplicates no landed run device: `Agent.runOps` folds it.

## 4. Effect on frozen surfaces

| Surface | Count | Breaker amendment? |
| --- | --- | --- |
| fields changed | 0 | no |
| frozen ascriptions or batteries altered | 0; every declaration is new | no |
| landed definitions or statements edited | 0 | no |
| frozen `mk` ascriptions | 5, untouched | no |
| production docstrings that become stale | none required; `Readable.error`'s and `Ordering.register`'s docstrings may name the departures of rows 006 and 007, builder-owned | no |
| graph documents | the cells of 2.10 gain grounds at landing (coordinator) | no |

Measured by building nothing in the tree: the prototypes elaborate against
the built libraries with no edit to any tracked file `[C]`
(`git status --short` empty before the document was written).

## 5. Effect on the trust gate, the strict ceiling and the libraries

- No gate change. The views declare no syntax and run no metaprogram; the
  prototypes' only metaprogramming is the scratch axiom receipt and `#eval`,
  which stay outside the tree. R-W1(c) and (d) hold with no addendum `[S]`.
- Strict ceiling: every prototype constant reaches `propext` and
  `Quot.sound` at most `[P]`; a builder who writes `simp` for `n == n` or
  `omega` under an `≠` hypothesis reaches `Classical.choice`, and the gate
  refuses it at build time `[C]` (2.1).
- Module closure (V2c rule 5): each new module must be imported from
  `Whatwg/Streams.lean`.
- Library cost: `WhatwgStreams`'s closure gains `Whatwg.Ecma262.Agent` and
  `Whatwg.Ecma262.AgentLaws`, already in `defaultTargets` `[H]` for the
  timing.
- Declaration snapshot: the prefix `Whatwg.Streams.Views` is a candidate for
  `recordedPrefixes` at the first records packet (R-W17: a breaker's).
- Freeze registry: if R-W5's conversion has landed when the W8b breaker
  freezes, its batteries use `#whatwg_freeze` with `axioms [propext,
  Quot.sound]`; otherwise `#check`, and the conversion absorbs them. No
  `*AxiomReport.lean` (R-W9).

## 6. Slices (question g)

### 6.1 Breaker packet

Contract `test/contracts/streams-agent-views.contract.md`, freezing: the
declaration record of section 3 for W8b.1 to W8b.5; the layout (writable
identity; readable closed at `0`, read `k` at `k + 1`); `CellValue`; the
function-record convention (`2 * id`, `2 * id + 1`, fired exactly when
settled); decisions 4 to 6 as ruled; the operation lists of the step bridges;
the masks. Under R-W9, every law not proved in this seat's prototype is
frozen only after the breaker proves it in scratch or evaluates it on
concrete runs, and the contract says which: proved here are the writable
squares, `agentView_wf`, the readable allocation and settle squares, the
settlement equation, and the five refutations of rows 001, 002, 004, 005 and
008; evaluated only are the three step bridges and rows 006, 007 and 009.

Batteries, red, in `test/fixtures/trust-gate/known-red.txt`:
`WhatwgTest/Streams/Views/CommonContract.lean`, `WritableContract.lean`,
`WritableStepContract.lean`, `ReadableContract.lean`,
`ReadableStepContract.lean`, `ConfigurationContract.lean`, one per builder
slice; witnesses in `WhatwgTest/Streams/Counterexamples/Views/Views.lean`.

Counterexample rows, family `WS-VIEW-CE`, registered before any
implementation:

| Id | Attack | Discriminating statement or witness |
| --- | --- | --- |
| `WS-VIEW-CE-001` | a Streams state is a lens target for the agent, so `handlerAt` can host it | `wView_no_lens` |
| `WS-VIEW-CE-002` | one function view of a readable/writable pair with one cursor | `pair_no_address_function` |
| `WS-VIEW-CE-003` | disjoint identity ranges by injection keep the allocation squares | the injection layout's two allocation squares imply the hypotheses of 002; the instance is owed by the breaker `[H]` |
| `WS-VIEW-CE-004` | the writable view of `initial` is Q5b-`Coherent` | `wView_initial_not_settledTraced` with `wView_initial_wf` |
| `WS-VIEW-CE-005` | the readable settle square needs no pending hypothesis | `rView_settleRead_unguarded` |
| `WS-VIEW-CE-006` | the readable error step needs no handled mark (`ReadableStreamError` step 7) | the error step of probe run `runR2` without `markHandled 0` |
| `WS-VIEW-CE-007` | the configuration's handled bits suffice (`PerformPromiseThen` step 12) | a registration step of each probe run without the derived bit |
| `WS-VIEW-CE-008` | `Transform.reactions` can be an agent's reactions | `reactions_cursor_decreases` |
| `WS-VIEW-CE-009` | Q4's `Ordering.reactions` can be the configuration view's reactions | a rejection step of probe run `run3` |
| `WS-VIEW-CE-010` | a function view can carry a foreign promise's cell (the sink or pull promise) | a writable run where the in-flight write's job runs and the cell would leave the view, against `Le.allocated`; owed with a witness by the breaker `[H]` |

### 6.2 Builder slices

| Slice | File fence | Content | Depends on | Size `[H]` |
| --- | --- | --- | --- | --- |
| W8b.1 | `Whatwg/Streams/Views/Common.lean`, `Whatwg/Streams/Views/Writable.lean`, two imports in `Whatwg/Streams.lean`, root imports, its `known-red.txt` lines | 3.1, 3.2 | packet | 450 lines; the prototype has 475 with refutations and docstrings |
| W8b.2 | `Whatwg/Streams/Views/WritableStep.lean`, one import | 3.3: `StoreFresh` through `fun_cases` on `tick` (76 cases) and `decide` (16), as W8a's `QueueInv`; the step bridge; the run corollaries through `Kernel.Path.lift` and `Agent.WF.runOps` | W8b.1 | 600 to 900 lines |
| W8b.3 | `Whatwg/Streams/Views/Readable.lean`, one import | 3.4 store half | W8b.1 | 400 lines |
| W8b.4 | `Whatwg/Streams/Views/ReadableStep.lean`, one import | 3.4 step half; `runPullJob` as its own lemma, since `Readable.Steps` is external-only | W8b.3 | 400 lines |
| W8b.5 | `Whatwg/Streams/Views/Configuration.lean`, one import | 3.5 | W8b.2 | 700 lines |

Order: W8b.1; then W8b.2 and W8b.3 in two worktrees; then W8b.4 and W8b.5.
Every slice runs the gate's strict ceiling by `Lean.collectAxioms` in a
scratch script while its battery is red (R-W9).

### 6.3 Graph and ledger

A new graph `STREAMS-PG-AGENT-VIEWS` in `docs/STREAMS-VIEWS-DAG.md`
(decision 7), born in the ledger (`WhatwgTest/Ledger/StreamsViews.lean`, a
ledger slice's file, not W8b's), every edge `required-open` at freeze; its
bridges edge names `WRITABLE-PG-DEFAULT`, `READABLE-PG-DEFAULT`,
`CONFIGURATION-PG-ORDERING` and `PROMISE-PG-AGENT`. The cells of 2.10 gain
grounds by ruling at landing, written as edge tokens.

### 6.4 What the independent reviewer checks

- `git diff --stat` against the slice base touches only the fence; the
  fingerprint shows only additions under `Whatwg.Streams.Views` and no
  changed constant.
- Each square's right side is the landed agent operation, not a copy.
- The layout: the readable's closed promise is allocated before every read in
  every reachable state, so identity `0` is honest; the generation view is
  out of scope and said so.
- Fidelity against the sealed bytes for the two derived bits:
  `ReadableStreamError` step 7 and `PerformPromiseThen` step 12.
- The configuration view's listed/held rule against THEN steps 9 to 11, and
  its activation reading of sink and start tokens as host activations.
- Masks by the rule of section 1 of this document; no `m1`, `m2` names.
- The gate line, `leanchecker` over the three prefixes, and the trust
  self-test (judged on `main`, R-W12).

### 6.5 Dependencies

Q5 B1 and B2 are on `main` (R-W16), as R-W4 requires. Q5b's `Coherent` is
needed only for the `Coherent` transfer statements; W8b.1 to W8b.4 do not
wait for it. W8a's `Kernel.Path.lift` and `Ordering.RegistrationsFresh` are
used. The freeze registry and the ledger: 5 and 6.3. P8: the composite
relation, the value map, foreign-promise cells. P12: the face corollary and
the Streams face.

## 7. Decisions for the coordinator (question h)

1. **View shape.** (a) total functions for the writable, the readable and the
   configuration, with per-operation squares and step bridges; composites and
   foreign-reaction jobs as a relation over an allocation log in P8 —
   recommended. (b) a relation `Views s a` for every calculus now: uniform,
   but every statement gains an existential, no view reads by `rfl`, and a
   breaker cannot evaluate a relation on concrete runs. (c) lens pairs:
   refuted (`WS-VIEW-CE-001`).
2. **Value types.** (a) `Views.CellValue α` for the readable, `Unit` for the
   writable and the configuration, composites later through a value map —
   recommended. (b) one agent per table: the readable alone needs two.
   (c) core `Sum Unit (ReadResult α)`: no new type, worse statements, the same
   existing-type row.
3. **Identities.** (a) identity inside the writable and the configuration,
   the fixed layout inside the readable, an allocation log across owners in
   P8 — recommended. (b) disjoint ranges by injection: refuted
   (`WS-VIEW-CE-002`, `003`). (c) give the closed promise an identity in the
   state: a field change, which R-W4 forbids.
4. **The readable's closed handled bit.** (a) derived from the status, so the
   error step's operation list carries `ReadableStreamError` step 7 —
   recommended. (b) constant `false`, with step 7 recorded as a P4 departure.
   Cost of (a): the view states a bit the calculus has no slot for, and the
   reviewer checks it against the bytes.
5. **The configuration's handled bit.** (a) derived from the registrations
   (THEN step 12) — recommended. (b) the writable's bits only, with
   `Ordering.register`'s departure recorded and `perform` not matched.
6. **The writable's initial settlement.** (a) the view's settlements are
   exactly `settlementTrace`, so P5's local M2 component is the agent's, and
   `Coherent` fails at a positive-high-water-mark `initial`
   (`WS-VIEW-CE-004`) — recommended. (b) prefix the settled cells the trace
   lacks, in table order, which makes the view `Coherent` and invents a
   position for a settlement P5 does not observe.
7. **Assurance route.** (a) one new graph `STREAMS-PG-AGENT-VIEWS`, since a
   view with bridges is a refinement relation, graph-bearing under
   `docs/AGENT-ROUTING.md`'s threshold — recommended. (b) receipts on each
   calculus graph's representation and bridges edges: no new document, but
   five graphs carry pieces of one relation.
8. **The face corollary** (`wView_resolvedWith`). (a) P12, beside the Streams
   face — recommended. (b) a module `Whatwg/Signatures/StreamsViews.lean` in
   W8b, in `PROMISE-PG-AGENT`'s library.
9. **Scope.** (a) W8b.1 to W8b.5 — recommended. (b) the configuration view
   moves to P8, since it is the slice with the trace-derived split. Cost of
   (b): the observer queue, the one place "one job queue" is reached in this
   lane, waits.
10. **Counterexample family.** `WS-VIEW-CE-001` onward — recommended.
11. **`stateMap`'s owner.** (a) a helper in `Views.Common` now, moved to
    `Whatwg.Ecma262.Promise` as `State.map` by a later PROMISE-PG-FIRST
    packet — recommended; (b) a Q-packet first.
12. **The composite relation and the value map.** (a) P8 — recommended;
    (b) a W8b.6 slice now: the log type, the relation, and the transform's
    and pipe's allocation squares.

## 8. Not checked

- The three step bridges are evaluated on 171 concrete steps and not proved;
  that every step keeps `StoreFresh` is not proved for any calculus.
- The readable view's `WF` transfer; the readable's settled-allocation
  squares, `streamClose` and `error` operation lists; the adapter to
  `readTable`.
- The configuration view's `WF`, its step bridge proof, and the claim that
  every observer token names a settled registration on reachable
  configurations.
- Q5b's `Coherent`, `Extends`, `postFrom` and `ImplementsFrom` were read in
  the frozen contract only; clause 17 was restated in scratch and refuted
  against it, not against the built definition.
- `WS-VIEW-CE-010`'s witness; the composite relation; the value map.
- No prototype was placed in the tree: `lake build` with the views, the
  trust self-test, `leanchecker` and the elaboration cost of the step-bridge
  proofs were not run. `WhatwgStreams`'s build cost with the new imports is
  not measured.
- lean4-effect4: read at one commit through greps, `git diff --stat`, one
  file read in full (`Refinement.lean`) and a helper seat's report; no Lean
  file there was built.
- The P12 face's needs in 2.10 are a design reading, not prototyped.

## Appendix A. Prototype sources

Each file elaborated as listed with `lake env lean <file>` from this seat's
worktree at `fea99fb`, in the scratch directory, and was not committed. They
are design evidence, not a builder's starting point that a breaker is bound
by. The `*Axioms.lean` variants are each file with `import Lean` prepended and
appendix A.6 appended.

### A.1 `W8bWritable.lean`

The writable store view, its squares, the `WF` transfer, the face corollary, and the refutations `wView_initial_not_settledTraced`, `wView_no_lens`, `no_address_function` and `pair_no_address_function`.

```lean
import Whatwg.Streams.Writable.Laws
import Whatwg.Ecma262.AgentLaws
import Whatwg.Signatures.Ecma262

/-!
# W8b prototype: the writable store view into the agent record

Scratch only. The view fills the agent's table with the landed
`Writable.promiseTable`, stores one resolving-function record per allocated
cell at function identities `2 * id` and `2 * id + 1` (fired exactly when the
cell is settled), sets the function cursor to `2 * nextPromise`, and reads the
settlement trace from the writable trace. Reactions, held records, the queue
and the activation are those of an agent with no consumer: the writable
calculus registers no reaction on a promise of its own table, and its sink
jobs react to foreign promises the table does not hold.
-/

namespace W8bProto

open Whatwg.Streams Whatwg.Ecma262

/-- The capability the view gives the cell `id`. -/
def capOf (id : Nat) : Promise.Capability := ⟨id, 2 * id, 2 * id + 1⟩

/-- One stored resolving-function record per allocated cell; fired exactly when
the cell is settled. -/
def fnOf {v r : Type} (e : Nat × Promise.State v r) : Promise.ResolvingFunctions :=
  ⟨e.1, 2 * e.1, 2 * e.1 + 1, match e.2 with | .pending => false | _ => true⟩

/-- The writable store view. -/
def wView {α ε body : Type} (s : Writable.State α ε) :
    Agent.Agent Unit (Boundary.Exception ε) body :=
  ⟨Writable.promiseTable s, Promise.Reactions.empty, [], Jobs.Queue.empty,
    s.promises.map fnOf, 2 * s.nextPromise, .checkpoint, none,
    Writable.settlementTrace s⟩

/-! ## The four store squares -/

/-- Allocating a pending cell is `Agent.newPromise` under the view, and the
identity it returns is the capability's promise. -/
theorem wView_freshPromise_pending {α ε body : Type} (s : Writable.State α ε)
    (h : s.nextPromise ∉ s.handled) :
    (wView (body := body) (Writable.freshPromise s .pending).1 =
        (Agent.newPromise (wView (body := body) s)).1) ∧
      (Writable.freshPromise s .pending).2 = (Agent.newPromise (wView (body := body) s)).2.promise := by
  have htab : Writable.promiseTable (Writable.freshPromise s .pending).1 =
      (Promise.Table.fresh (Writable.promiseTable s) .pending).1 :=
    congrArg Prod.fst (Writable.freshPromise_bridge s .pending h)
  refine ⟨?_, rfl⟩
  rw [Agent.newPromise_eq]
  show Agent.Agent.mk _ _ _ _ _ _ _ _ _ = Agent.Agent.mk _ _ _ _ _ _ _ _ _
  congr 1
  · show (s.promises ++ [(s.nextPromise, Promise.State.pending)]).map fnOf = _
    rw [List.map_append]
    rfl

/-- Doubling is injective on `Nat`, as a `BEq` equation. Written without
`simp` or `omega`, both of which reach `Classical.choice` here. -/
theorem two_mul_beq (a b : Nat) : (2 * a == 2 * b) = (a == b) := by
  cases h : (a == b) with
  | true => rw [beq_iff_eq.mp h]; exact beq_iff_eq.mpr rfl
  | false =>
      cases h2 : (2 * a == 2 * b) with
      | false => rfl
      | true =>
          have hab := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (beq_iff_eq.mp h2)
          rw [hab, beq_iff_eq.mpr (rfl : b = b)] at h
          cases h

/-- The pick of the cell `id`'s resolve function, read through `fnOf`. -/
theorem pick_resolve {v r : Type} (id : Nat) (e : Nat × Promise.State v r) :
    ((fnOf e).resolve == (capOf id).resolve) = (e.1 == id) :=
  two_mul_beq e.1 id

/-- The pick of the cell `id`'s reject function, read through `fnOf`. -/
theorem pick_reject {v r : Type} (id : Nat) (e : Nat × Promise.State v r) :
    ((fnOf e).reject == (capOf id).reject) = (e.1 == id) := by
  show (2 * e.1 + 1 == 2 * id + 1) = (e.1 == id)
  rw [← two_mul_beq e.1 id]
  cases h : (2 * e.1 == 2 * id) with
  | true => rw [beq_iff_eq.mp h]; exact beq_iff_eq.mpr rfl
  | false =>
      cases h2 : (2 * e.1 + 1 == 2 * id + 1) with
      | false => rfl
      | true =>
          rw [Nat.add_right_cancel (beq_iff_eq.mp h2), beq_iff_eq.mpr (rfl : 2 * id = 2 * id)] at h
          cases h

/-- Finding a record by a pick that selects exactly the records of cell `id`
is finding the first cell `id`. -/
theorem find_fnOf {v r : Type} (l : List (Nat × Promise.State v r)) (id : Nat)
    (pick : Promise.ResolvingFunctions → Bool)
    (hpick : ∀ e : Nat × Promise.State v r, pick (fnOf e) = (e.1 == id)) :
    (l.map fnOf).find? pick = (l.find? (fun e => e.1 == id)).map fnOf := by
  rw [List.find?_map]
  have : (pick ∘ fnOf) = (fun (e : Nat × Promise.State v r) => e.1 == id) := by
    funext e; exact hpick e
  rw [this]

/-- Marking the records a pick selects is mapping the settled cells through
`fnOf`, when the pick selects exactly the records of cell `id`. -/
theorem mark_fnOf {v r : Type} (l : List (Nat × Promise.State v r)) (id : Nat)
    (pick : Promise.ResolvingFunctions → Bool)
    (hpick : ∀ e : Nat × Promise.State v r, pick (fnOf e) = (e.1 == id))
    (settled : Promise.State v r) (hs : settled ≠ .pending) :
    (l.map fnOf).map (fun g => if pick g then { g with alreadyResolved := true } else g) =
      (l.map (fun e => if e.1 == id then (id, settled) else e)).map fnOf := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro e _
  show (if pick (fnOf e) then { fnOf e with alreadyResolved := true } else fnOf e) =
    fnOf (if e.1 == id then (id, settled) else e)
  rw [hpick e]
  cases h : (e.1 == id) with
  | false => rfl
  | true =>
      have he : e.1 = id := beq_iff_eq.mp h
      show ({ fnOf e with alreadyResolved := true } : Promise.ResolvingFunctions) = fnOf (id, settled)
      cases settled with
      | pending => exact absurd rfl hs
      | fulfilled _ => simp only [fnOf, he]
      | rejected _ => simp only [fnOf, he]

/-- Settling a cell of the writable table is calling its stored resolving
function under the view, unconditionally: a missing cell has no record, a
settled cell's record has fired, and a pending cell's record settles it and
appends the settlement. The pick is either of the cell's two functions. -/
theorem wView_settle {α ε body : Type} (s : Writable.State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) Unit)
    (pick : Promise.ResolvingFunctions → Bool)
    (hpick : ∀ e : Nat × Promise.State Unit (Boundary.Exception ε), pick (fnOf e) = (e.1 == id)) :
    wView (body := body) (Writable.settle s id result) =
      Agent.callFunctions (wView (body := body) s) pick result := by
  have hfind : (wView (body := body) s).functions.find? pick =
      (s.promises.find? (fun p => p.1 == id)).map fnOf := find_fnOf s.promises id pick hpick
  have hlook : Writable.lookupPromise s id = (s.promises.find? (fun p => p.1 == id)).map Prod.snd :=
    rfl
  cases hf : s.promises.find? (fun p => p.1 == id) with
  | none =>
      rw [hf] at hfind hlook
      rw [Agent.callFunctions_none _ _ _ hfind]
      unfold Writable.settle
      rw [hlook]
      rfl
  | some e =>
      rw [hf] at hfind hlook
      have he1 : e.1 = id := beq_iff_eq.mp
        (List.find?_some (p := fun (p : Nat × Promise.State Unit (Boundary.Exception ε)) => p.1 == id) hf)
      cases hst : e.2 with
      | fulfilled u =>
          have hfired : (fnOf e).alreadyResolved = true := by simp only [fnOf, hst]
          rw [Agent.callFunctions_fired _ _ _ (fnOf e) hfind hfired]
          unfold Writable.settle
          rw [hlook]
          simp only [Option.map_some, hst]
          rfl
      | rejected x =>
          have hfired : (fnOf e).alreadyResolved = true := by simp only [fnOf, hst]
          rw [Agent.callFunctions_fired _ _ _ (fnOf e) hfind hfired]
          unfold Writable.settle
          rw [hlook]
          simp only [Option.map_some, hst]
          rfl
      | pending =>
          have hfresh : (fnOf e).alreadyResolved = false := by simp only [fnOf, hst]
          rw [Agent.callFunctions_fresh _ _ _ (fnOf e) hfind hfresh]
          have hpend : Promise.Table.isPending (Writable.promiseTable s) id = true := by
            rw [Promise.Table.isPending_iff, ← Writable.lookupPromise_bridge, hlook]
            simp only [Option.map_some, hst]
          have htab := Writable.settle_bridge s id result
          have hpend' : Promise.Table.isPending (wView (body := body) s).table id = true := hpend
          have hws : Writable.settle s id result =
              { s with
                promises := s.promises.map (fun p => if p.1 == id then
                  (id, match result with | .ok _ => .fulfilled () | .error e => .rejected e) else p),
                trace := s.trace ++ [.settled id result] } := by
            unfold Writable.settle
            rw [hlook]
            simp only [Option.map_some, hst]
            rfl
          rw [Agent.settle_eq, show (fnOf e).promise = id from he1]
          unfold Promise.Table.settleAndTrigger Promise.Table.settleTraced
          rw [hpend']
          simp only [if_true]
          show Agent.Agent.mk _ _ _ _ _ _ _ _ _ = Agent.Agent.mk _ _ _ _ _ _ _ _ _
          congr 1
          · cases result <;> rfl
          · cases result <;> rfl
          · rw [hws]
            refine (mark_fnOf s.promises id pick hpick _ ?_).symm
            cases result <;> exact fun h => by cases h
          · rw [hws]
            show List.filterMap _ (s.trace ++ [.settled id result]) = _
            rw [List.filterMap_append]
            rfl

/-- Fulfilling a writable cell is `Agent.resolve` through its capability. -/
theorem wView_settle_ok {α ε body : Type} (s : Writable.State α ε) (id : Nat) :
    wView (body := body) (Writable.settle s id (.ok ())) =
      Agent.resolve (wView (body := body) s) (capOf id) () :=
  wView_settle s id (.ok ()) _ (pick_resolve id)

/-- Rejecting a writable cell is `Agent.reject` through its capability. -/
theorem wView_settle_error {α ε body : Type} (s : Writable.State α ε) (id : Nat)
    (e : Boundary.Exception ε) :
    wView (body := body) (Writable.settle s id (.error e)) =
      Agent.reject (wView (body := body) s) (capOf id) e :=
  wView_settle s id (.error e) _ (pick_reject id)

/-- Marking a writable cell handled is `Agent.markHandled`. -/
theorem wView_markHandled {α ε body : Type} (s : Writable.State α ε) (id : Nat) :
    wView (body := body) (Writable.markHandled s id) =
      Agent.markHandled (wView (body := body) s) id := by
  have htab := Writable.markHandled_bridge s id
  have hm : Writable.markHandled s id = s ∨ Writable.markHandled s id = { s with handled := s.handled ++ [id] } := by
    unfold Writable.markHandled
    cases h : decide (id ∈ s.handled) with
    | true => exact Or.inl (if_pos (of_decide_eq_true h))
    | false => exact Or.inr (if_neg (of_decide_eq_false h))
  have hp : (Writable.markHandled s id).promises = s.promises := by
    rcases hm with h | h <;> rw [h]
  have hn : (Writable.markHandled s id).nextPromise = s.nextPromise := by
    rcases hm with h | h <;> rw [h]
  have ht : (Writable.markHandled s id).trace = s.trace := by
    rcases hm with h | h <;> rw [h]
  show (⟨Writable.promiseTable (Writable.markHandled s id), Promise.Reactions.empty, [],
      Jobs.Queue.empty, (Writable.markHandled s id).promises.map fnOf,
      2 * (Writable.markHandled s id).nextPromise, .checkpoint, none,
      (Writable.markHandled s id).trace.filterMap _⟩ : Agent.Agent Unit (Boundary.Exception ε) body) = _
  rw [htab, hp, hn, ht]
  rfl

/-- A cell born fulfilled is the pending allocation followed by its own
settlement, provided no earlier cell carries the cursor. -/
theorem freshPromise_fulfilled_split {α ε : Type} (s : Writable.State α ε)
    (h2 : ∀ p ∈ s.promises, p.1 ≠ s.nextPromise) :
    (Writable.freshPromise s (.fulfilled ())).1 =
      Writable.settle (Writable.freshPromise s .pending).1 s.nextPromise (.ok ()) := by
  have hnone : s.promises.find? (fun p => p.1 == s.nextPromise) = none := by
    rw [List.find?_eq_none]
    intro p hp hb
    exact h2 p hp (beq_iff_eq.mp hb)
  have hlook : Writable.lookupPromise (Writable.freshPromise s .pending).1 s.nextPromise =
      some .pending := by
    show Option.map Prod.snd (List.find? (fun p => p.1 == s.nextPromise)
      (s.promises ++ [(s.nextPromise, Promise.State.pending)])) = _
    have hself' : ((fun (p : Nat × Writable.UnitPromise ε) => p.1 == s.nextPromise)
        (s.nextPromise, Promise.State.pending)) = true := beq_iff_eq.mpr rfl
    rw [List.find?_append, hnone, Option.none_or,
      List.find?_cons_of_pos (p := fun (p : Nat × Writable.UnitPromise ε) => p.1 == s.nextPromise)
        hself']
    rfl
  have hkeep : s.promises.map (fun p => if p.1 == s.nextPromise then
      (s.nextPromise, (Promise.State.fulfilled () : Writable.UnitPromise ε)) else p) =
      s.promises := by
    conv => rhs; rw [← List.map_id s.promises]
    apply List.map_congr_left
    intro p hp
    have : (p.1 == s.nextPromise) = false := by
      cases hb : (p.1 == s.nextPromise) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hb) (h2 p hp)
    rw [this]; rfl
  have hself : (s.nextPromise == s.nextPromise) = true := beq_iff_eq.mpr rfl
  have hws : Writable.settle (Writable.freshPromise s .pending).1 s.nextPromise (.ok ()) =
      { (Writable.freshPromise s .pending).1 with
        promises := (s.promises ++ [(s.nextPromise, Promise.State.pending)]).map
          (fun (p : Nat × Writable.UnitPromise ε) => if p.1 == s.nextPromise then
            (s.nextPromise, (Promise.State.fulfilled () : Writable.UnitPromise ε)) else p),
        trace := s.trace ++ [Writable.Event.settled s.nextPromise (.ok ())] } := by
    unfold Writable.settle
    rw [hlook]
    rfl
  rw [hws, List.map_append, hkeep, List.map_cons, List.map_nil, hself, if_pos rfl]
  rfl

/-- **"A promise resolved with" under the view.** Allocating a cell born
fulfilled is Web IDL "a promise resolved with" (`Agent.newPromise` then
`Agent.resolve` through the new capability), provided the cursor is fresh and
not marked handled. DB-04 M2 (it observes the settlement trace). -/
theorem wView_freshPromise_fulfilled {α ε body : Type} (s : Writable.State α ε)
    (h1 : s.nextPromise ∉ s.handled) (h2 : ∀ p ∈ s.promises, p.1 ≠ s.nextPromise) :
    wView (body := body) (Writable.freshPromise s (.fulfilled ())).1 =
      Agent.resolve (Agent.newPromise (wView (body := body) s)).1
        (Agent.newPromise (wView (body := body) s)).2 () := by
  rw [freshPromise_fulfilled_split s h2, wView_settle_ok, (wView_freshPromise_pending s h1).1]
  rfl

/-! ## Invariant transfer: `WF` of the view -/

/-- The writable cell invariant the view's `WF` needs: identities unique and
below the cursor (the first two conjuncts of the W8 design's
`CellsWellFormed`). -/
def CellsFresh {α ε : Type} (s : Writable.State α ε) : Prop :=
  (s.promises.map Prod.fst).Nodup ∧ ∀ p ∈ s.promises, p.1 < s.nextPromise

/-- The writable trace agrees with the table: no identity settles twice, and
each recorded settlement is the cell's present state. -/
def TraceCoherent {α ε : Type} (s : Writable.State α ε) : Prop :=
  ((Writable.settlementTrace s).map Prod.fst).Nodup ∧
    (∀ (p : Nat) (v : Unit), (p, Except.ok v) ∈ Writable.settlementTrace s →
      Writable.lookupPromise s p = some (.fulfilled v)) ∧
    (∀ (p : Nat) (r : Boundary.Exception ε), (p, Except.error r) ∈ Writable.settlementTrace s →
      Writable.lookupPromise s p = some (.rejected r))

/-- With unique keys, lookup finds the member itself. -/
theorem find?_of_nodup {β : Type} (l : List (Nat × β)) (p : Nat × β)
    (hn : (l.map Prod.fst).Nodup) (hp : p ∈ l) :
    l.find? (fun e => e.1 == p.1) = some p := by
  induction l with
  | nil => cases hp
  | cons x xs ih =>
      rw [List.map_cons, List.nodup_cons] at hn
      cases hx : (x.1 == p.1) with
      | true =>
          rw [List.find?_cons_of_pos (p := fun (e : Nat × β) => e.1 == p.1) hx]
          rcases List.mem_cons.mp hp with h | h
          · rw [h]
          · exact absurd (List.mem_map_of_mem (f := Prod.fst) h)
              (by rw [← beq_iff_eq.mp hx]; exact hn.1)
      | false =>
          rw [List.find?_cons_of_neg (p := fun (e : Nat × β) => e.1 == p.1) (by rw [hx]; simp)]
          rcases List.mem_cons.mp hp with h | h
          · rw [h] at hx; exact absurd hx (by rw [beq_iff_eq.mpr rfl]; simp)
          · exact ih hn.2 h

/-- **`WF` transfers to the view** under the writable cell invariant and trace
coherence. Each of the fourteen clauses is discharged; nine hold for every
writable state because the view stores no reaction, held record or job. -/
theorem wView_wf {α ε body : Type} (s : Writable.State α ε) (hc : CellsFresh s)
    (ht : TraceCoherent s) : Agent.WF (wView (body := body) s) := by
  have hlookup : ∀ p ∈ s.promises, Writable.lookupPromise s p.1 = some p.2 := by
    intro p hp
    show Option.map Prod.snd (s.promises.find? (fun e => e.1 == p.1)) = _
    rw [find?_of_nodup s.promises p hc.1 hp]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((s.promises.map _).map Prod.fst).Nodup
    rw [List.map_map]
    exact hc.1
  · intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hc.2 p hp
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    have := hc.2 p hp
    exact ⟨rfl, by show 2 * p.1 + 1 < 2 * s.nextPromise; omega⟩
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    show (Option.map Prod.snd (List.find? (fun e => e.1 == p.1) (s.promises.map
      (fun (q : Nat × Writable.UnitPromise ε) =>
        (q.1, Promise.Cell.mk q.2 (Decidable.decide (q.1 ∈ s.handled))))))).isSome = true
    rw [List.find?_map, Option.isSome_map, Option.isSome_map]
    have h := find?_of_nodup s.promises p hc.1 hp
    have hc' : ((fun (e : Nat × Promise.Cell Unit (Boundary.Exception ε)) => e.1 == p.1) ∘
        (fun (q : Nat × Writable.UnitPromise ε) =>
          (q.1, Promise.Cell.mk q.2 (Decidable.decide (q.1 ∈ s.handled))))) =
        (fun (e : Nat × Writable.UnitPromise ε) => e.1 == p.1) := rfl
    rw [hc', h]
    rfl
  · intro f hf hfired
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    have hget : Promise.Table.get (Writable.promiseTable s) p.1 = some p.2 := by
      rw [← Writable.lookupPromise_bridge]; exact hlookup p hp
    show Promise.Table.isPending (Writable.promiseTable s) p.1 = false
    unfold Promise.Table.isPending
    rw [hget]
    cases hs : p.2 with
    | pending => simp only [fnOf, hs] at hfired; cases hfired
    | fulfilled _ => rfl
    | rejected _ => rfl
  · intro r hr; change r ∈ ([] : List (Promise.Reaction body)) at hr; cases hr
  · intro j hj; cases hj
  · rfl
  · show ((s.promises.map fnOf).map Promise.ResolvingFunctions.resolve).Nodup
    have heq : (s.promises.map fnOf).map Promise.ResolvingFunctions.resolve =
        (s.promises.map Prod.fst).map (fun k => 2 * k) := by
      rw [List.map_map, List.map_map]; rfl
    rw [heq]
    exact List.Pairwise.map (fun k => 2 * k) (fun a b h heq => h (by omega)) hc.1
  · exact List.nodup_nil
  · intro j hj; cases hj
  · exact ⟨fun j hj => (by cases hj), fun n hn => (by cases hn)⟩
  · intro r hr; change r ∈ ([] : List (Promise.Reaction body)) at hr; cases hr
  · refine ⟨ht.1, ?_, ?_⟩
    · intro p v hm
      show Promise.Table.get (Writable.promiseTable s) p = _
      rw [← Writable.lookupPromise_bridge]; exact ht.2.1 p v hm
    · intro p r hm
      show Promise.Table.get (Writable.promiseTable s) p = _
      rw [← Writable.lookupPromise_bridge]; exact ht.2.2 p r hm

/-! ## A composite store operation as a run of agent operations -/

/-- `op.writable-stream-default-writer-ensure-ready-promise-rejected` on a
pending ready promise is the two-operation agent run "reject through the ready
promise's capability, then mark it handled". DB-04 M2. -/
theorem wView_ensureReadyRejected_pending {α ε body : Type} (s : Writable.State α ε)
    (e : Boundary.Exception ε) (h : Writable.lookupPromise s s.readyPromise = some .pending) :
    wView (body := body) (Writable.ensureReadyRejected s e) =
      (Agent.runOps (wView (body := body) s)
        [.reject (capOf s.readyPromise) e, .markHandled s.readyPromise]).1 := by
  rw [Writable.ensureReadyRejected_pending s e h, wView_markHandled, wView_settle_error]
  rfl

/-! ## The face: a cell born fulfilled is the face's "a promise resolved with" -/

/-- Running the face's two-operation program `resolvedWith ()` on the view of a
writable state answers the capability of the cell `freshPromise` allocates born
fulfilled, and leaves the view of the state it leaves. DB-04 M2. -/
theorem wView_resolvedWith {α ε body : Type} (s : Writable.State α ε)
    (h1 : s.nextPromise ∉ s.handled) (h2 : ∀ p ∈ s.promises, p.1 ≠ s.nextPromise) :
    Whatwg.Signatures.Ecma262.run (Whatwg.Signatures.Ecma262.resolvedWith (body := body) ())
        (wView (body := body) s) =
      (capOf (Writable.freshPromise s (.fulfilled ())).2,
        wView (body := body) (Writable.freshPromise s (.fulfilled ())).1) := by
  rw [Whatwg.Signatures.Ecma262.run_resolvedWith, wView_freshPromise_fulfilled s h1 h2]
  rfl

/-! ## Refutations -/

/-- Clause 17 of addendum Q5b (`settledTraced`), written out here because the
addendum is not on this base: every settled cell is in the settlement trace. -/
def SettledTraced {v r b : Type} (a : Agent.Agent v r b) : Prop :=
  (∀ (p : Nat) (x : v), Promise.Table.get a.table p = some (.fulfilled x) →
      (p, Except.ok x) ∈ a.settlements) ∧
    (∀ (p : Nat) (e : r), Promise.Table.get a.table p = some (.rejected e) →
      (p, Except.error e) ∈ a.settlements)

/-- Every algorithm slot empty. -/
def alg0 : Writable.Algorithms := ⟨none, none, none, none⟩

/-- The view of the writable initial state at a positive high-water mark is
well formed. -/
theorem wView_initial_wf :
    Agent.WF (wView (body := Unit)
      (Writable.initial (α := Unit) (ε := Unit) .posInfinity alg0 0 0)) :=
  wView_wf _ ⟨by decide, by decide⟩ (by
    refine ⟨List.nodup_nil, ?_, ?_⟩
    · intro p v h
      change (p, Except.ok v) ∈ ([] : List (Nat × Except (Boundary.Exception Unit) Unit)) at h
      cases h
    · intro p r h
      change (p, Except.error r) ∈ ([] : List (Nat × Except (Boundary.Exception Unit) Unit)) at h
      cases h)

/-- **Refuted (expected to hold).** The same view is not `settledTraced`:
`Writable.initial` stores the ready promise fulfilled with no `.settled`
event, where `freshPromise` records one for a cell born fulfilled. -/
theorem wView_initial_not_settledTraced :
    ¬ SettledTraced (wView (body := Unit)
      (Writable.initial (α := Unit) (ε := Unit) .posInfinity alg0 0 0)) := by
  intro h
  have hm := h.1 0 () rfl
  cases hm

/-- **Refuted (expected to hold).** No `update` makes the writable view a lens:
the view never shows a registered reaction, so `view (update a s) = a` fails at
an agent with one. `interpret_handlerAt`'s hypothesis therefore cannot be met
with `σ := Writable.State`. -/
theorem wView_no_lens {α ε body : Type} (s0 : Writable.State α ε) :
    ¬ ∃ update : Agent.Agent Unit (Boundary.Exception ε) body →
        Writable.State α ε → Writable.State α ε,
      ∀ a s, wView (update a s) = a := by
  intro ⟨update, h⟩
  have := congrArg (fun x => x.reactions.next)
    (h { Agent.empty with reactions := ⟨[], [], 1⟩ } s0)
  have h0 : (0 : Nat) = 1 := this
  exact absurd h0 (by decide)

/-! ## No function view of two independent cursors -/

/-- A typed address of a Streams promise cell. -/
inductive Addr where
  | readClosed
  | read (k : Nat)
  | writable (k : Nat)
  deriving DecidableEq, Repr

/-- **No address function for two independent allocators.** If a view assigns
the cell a first allocator creates to the one cursor, keeps an assigned address
across the second allocator, and advances the cursor on the second allocator,
and the two allocators commute, the cursor equals its successor. -/
theorem no_address_function {S A : Type} (s : S)
    (next : S → Nat) (allocW allocR : S → S) (newW : S → A) (addr : S → A → Option Nat)
    (hcomm : allocW (allocR s) = allocR (allocW s))
    (hnextR : next (allocR s) = next s + 1)
    (hassignW : ∀ t, addr (allocW t) (newW t) = some (next t))
    (hkeepR : ∀ t x, (addr t x).isSome = true → addr (allocR t) x = addr t x)
    (hnewW : newW (allocR s) = newW s) : False := by
  have h1 : addr (allocR (allocW s)) (newW s) = some (next s) := by
    rw [hkeepR (allocW s) (newW s) (by rw [hassignW]; rfl), hassignW]
  have h2 : addr (allocW (allocR s)) (newW (allocR s)) = some (next s + 1) := by
    rw [hassignW, hnextR]
  rw [hnewW, hcomm, h1] at h2
  have := Option.some.inj h2
  omega

/-- The readable and writable halves of a transform or a pipe: no function of
the pair, with one cursor and an address map, assigns a fresh writable cell to
the cursor, keeps addresses across a read-cell allocation and advances the
cursor on it. -/
theorem pair_no_address_function {α ε : Type} (s : Readable.State α ε × Writable.State α ε)
    (next : Readable.State α ε × Writable.State α ε → Nat)
    (addr : Readable.State α ε × Writable.State α ε → Addr → Option Nat)
    (hnextR : next ((Readable.freshReadCell s.1 .pending).1, s.2) = next s + 1)
    (hassignW : ∀ t : Readable.State α ε × Writable.State α ε,
      addr (t.1, (Writable.freshPromise t.2 .pending).1) (.writable t.2.nextPromise) = some (next t))
    (hkeepR : ∀ (t : Readable.State α ε × Writable.State α ε) (x : Addr), (addr t x).isSome = true →
      addr ((Readable.freshReadCell t.1 .pending).1, t.2) x = addr t x) : False :=
  no_address_function s next (fun t => (t.1, (Writable.freshPromise t.2 .pending).1))
    (fun t => ((Readable.freshReadCell t.1 .pending).1, t.2)) (fun t => .writable t.2.nextPromise)
    addr rfl hnextR hassignW hkeepR rfl

end W8bProto
```

### A.2 `W8bReadable.lean`

The readable store view with the closed promise at identity `0`, its allocation and settle squares, and the refutation `rView_settleRead_unguarded`.

```lean
import Whatwg.Streams.Readable.Laws
import Whatwg.Ecma262.AgentLaws

/-!
# W8b prototype: the readable store view, closed promise at address 0

Scratch only. The readable calculus holds two kinds of promise: the reader's
closed promise, by value and with no identity (`E-24`), and the read promises,
keyed by `nextRead`. The view gives them one table at one value type, the
tagged sum `CellValue α`, with a fixed layout: the closed promise is agent
identity `0` and read `k` is agent identity `k + 1`. One cursor,
`nextRead + 1`, serves both, because the closed promise is allocated with the
reader, before any read.
-/

namespace W8bRead

open Whatwg.Streams Whatwg.Ecma262

/-- The one value type of a readable view: the closed promise's `undefined`
or a read result. -/
inductive CellValue (α : Type) where
  | unit
  | read (r : Readable.ReadResult α)
  deriving DecidableEq, Repr

/-- A promise state at another value type. -/
def stateMap {v w r : Type} (f : v → w) : Promise.State v r → Promise.State w r
  | .pending => .pending
  | .fulfilled x => .fulfilled (f x)
  | .rejected e => .rejected e

/-- The agent identity of read `k`. -/
def readAddr (k : Nat) : Nat := k + 1

/-- The view's cells, closed promise first. -/
def rCells {α ε : Type} (s : Readable.State α ε) :
    List (Nat × Promise.State (CellValue α) (Boundary.Exception ε)) :=
  (0, stateMap (fun _ => CellValue.unit) s.closedPromise) ::
    s.readPromises.map (fun p => (readAddr p.1, stateMap CellValue.read p.2))

/-- `ReadableStreamError` step 7 sets the closed promise's
`[[PromiseIsHandled]]`; the readable calculus has no slot for it, so the view
reads it from the status. Read promises are never marked handled. -/
def handledAt {α ε : Type} (s : Readable.State α ε) (id : Nat) : Bool :=
  match id, s.status with
  | 0, .errored _ => true
  | _, _ => false

/-- One stored resolving-function record per cell, fired exactly when settled. -/
def fnOf {v r : Type} (e : Nat × Promise.State v r) : Promise.ResolvingFunctions :=
  ⟨e.1, 2 * e.1, 2 * e.1 + 1, match e.2 with | .pending => false | _ => true⟩

/-- A readable settlement at its agent identity and value type. -/
def settlementOf {α ε : Type} :
    Readable.Settlement α ε → Nat × Except (Boundary.Exception ε) (CellValue α)
  | .closed r => (0, r.map (fun _ => CellValue.unit))
  | .read id r => (readAddr id, r.map CellValue.read)

/-- The readable store view. -/
def rView {α ε body : Type} (s : Readable.State α ε) :
    Agent.Agent (CellValue α) (Boundary.Exception ε) body :=
  ⟨⟨(rCells s).map (fun e => (e.1, Promise.Cell.mk e.2 (handledAt s e.1))), s.nextRead + 1⟩,
    Promise.Reactions.empty, [], Jobs.Queue.empty, (rCells s).map fnOf, 2 * (s.nextRead + 1),
    .checkpoint, none, (Readable.settlementTrace s).map settlementOf⟩

/-- **Allocating a pending read is `Agent.newPromise`**, and the read's identity
is the new capability's promise less one. DB-04 M1. -/
theorem rView_freshReadCell_pending {α ε body : Type} (s : Readable.State α ε) :
    rView (body := body) (Readable.freshReadCell s .pending).1 =
        (Agent.newPromise (rView (body := body) s)).1 ∧
      readAddr (Readable.freshReadCell s .pending).2 =
        (Agent.newPromise (rView (body := body) s)).2.promise := by
  refine ⟨?_, rfl⟩
  rw [Agent.newPromise_eq]
  show Agent.Agent.mk _ _ _ _ _ _ _ _ _ = Agent.Agent.mk _ _ _ _ _ _ _ _ _
  congr 1
  · show Promise.Table.mk (List.map _ ((0, _) ::
        (s.readPromises ++ [(s.nextRead, Promise.State.pending)]).map _)) _ = _
    rw [List.map_append, ← List.cons_append, List.map_append]
    rfl
  · show List.map fnOf ((0, _) ::
        (s.readPromises ++ [(s.nextRead, Promise.State.pending)]).map _) = _
    rw [List.map_append, ← List.cons_append, List.map_append]
    rfl

/-- The readable settlement trace, read through the view, is the agent's
settlement trace: the closed entry carries identity `0`. This is the bridge
`E-63` deferred because the closed entry carried no identity. DB-04 M2. -/
theorem rView_settlements {α ε body : Type} (s : Readable.State α ε) :
    (rView (body := body) s).settlements = (Readable.settlementTrace s).map settlementOf := rfl

/-- The closed promise is the view's identity `0`, whatever the reads. DB-04 M1. -/
theorem rView_closed {α ε body : Type} (s : Readable.State α ε) :
    Promise.Table.get (rView (body := body) s).table 0 =
      some (stateMap (fun _ => CellValue.unit) s.closedPromise) := by
  show Option.map Promise.Cell.state (Option.map Prod.snd
    (List.find? (fun e => e.1 == 0) ((0, _) :: _))) = _
  rw [List.find?_cons_of_pos (p := fun (e : Nat × Promise.Cell (CellValue α) (Boundary.Exception ε)) =>
    e.1 == 0) (beq_iff_eq.mpr rfl)]
  rfl

/-! ## Settling a read -/

/-- The capability the view gives identity `id`. -/
def capOf (id : Nat) : Promise.Capability := ⟨id, 2 * id, 2 * id + 1⟩

/-- A read settled together with its trace event, the shape `continuePull`
and `beginEnqueue` give it. -/
def settleReadTraced {α ε : Type} (s : Readable.State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) (Readable.ReadResult α)) : Readable.State α ε :=
  { Readable.settleReadCell s id result with
    trace := s.trace ++ [.settled (.read id result)] }

/-- Successor is injective, as a `BEq` equation, without `simp` or `omega`. -/
theorem succ_beq (a b : Nat) : (a + 1 == b + 1) = (a == b) := by
  cases h : (a == b) with
  | true => rw [beq_iff_eq.mp h]; exact beq_iff_eq.mpr rfl
  | false =>
      cases h2 : (a + 1 == b + 1) with
      | false => rfl
      | true =>
          rw [Nat.add_right_cancel (beq_iff_eq.mp h2), beq_iff_eq.mpr (rfl : b = b)] at h
          cases h

/-- Doubling is injective, as a `BEq` equation, without `simp` or `omega`. -/
theorem two_mul_beq (a b : Nat) : (2 * a == 2 * b) = (a == b) := by
  cases h : (a == b) with
  | true => rw [beq_iff_eq.mp h]; exact beq_iff_eq.mpr rfl
  | false =>
      cases h2 : (2 * a == 2 * b) with
      | false => rfl
      | true =>
          have hab := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (beq_iff_eq.mp h2)
          rw [hab, beq_iff_eq.mpr (rfl : b = b)] at h
          cases h

/-- The shift a read cell takes into the view. -/
def shift {α ε : Type} (p : Nat × Readable.PromiseState (Readable.ReadResult α) ε) :
    Nat × Promise.State (CellValue α) (Boundary.Exception ε) :=
  (readAddr p.1, stateMap CellValue.read p.2)

/-- Lookup of a read's identity in the view's cells is lookup of the read. -/
theorem find_rCells {α ε : Type} (s : Readable.State α ε) (id : Nat) :
    (rCells s).find? (fun e => e.1 == readAddr id) =
      (s.readPromises.find? (fun p => p.1 == id)).map shift := by
  show List.find? _ ((0, _) :: s.readPromises.map shift) = _
  rw [List.find?_cons_of_neg (p := fun (e : Nat × Promise.State (CellValue α) (Boundary.Exception ε)) =>
      e.1 == readAddr id) (by show ¬ (0 == id + 1) = true; exact Bool.false_ne_true),
    List.find?_map]
  have : ((fun (e : Nat × Promise.State (CellValue α) (Boundary.Exception ε)) => e.1 == readAddr id) ∘
      shift) = (fun (p : Nat × Readable.PromiseState (Readable.ReadResult α) ε) => p.1 == id) := by
    funext p; exact succ_beq p.1 id
  rw [this]

/-- Settling read `id` updates the view's cells at identity `readAddr id` and
nowhere else; the closed cell keeps its identity `0`. -/
theorem rCells_settleRead {α ε : Type} (s : Readable.State α ε) (id : Nat)
    (x : Readable.ReadResult α) :
    rCells (settleReadTraced s id (.ok x)) =
      (rCells s).map (fun e => if e.1 == readAddr id then
        (e.1, Promise.State.fulfilled (CellValue.read x)) else e) := by
  show (0, stateMap (fun _ => CellValue.unit) s.closedPromise) ::
      (s.readPromises.map (fun p => if p.1 = id then (p.1, Promise.State.fulfilled x) else p)).map
        shift =
    List.map _ ((0, stateMap (fun _ => CellValue.unit) s.closedPromise) :: s.readPromises.map shift)
  rw [List.map_cons, List.map_map, List.map_map]
  have h0 : ((0 : Nat) == readAddr id) = false := rfl
  rw [h0]
  congr 1
  apply List.map_congr_left
  intro p _
  show shift (if p.1 = id then (p.1, Promise.State.fulfilled x) else p) =
    (if (p.1 + 1 == id + 1) = true then (p.1 + 1, Promise.State.fulfilled (CellValue.read x))
      else shift p)
  rw [succ_beq]
  cases hpid : decide (p.1 = id) with
  | false =>
      have hn : ¬ p.1 = id := of_decide_eq_false hpid
      have hb : (p.1 == id) = false := by
        cases hb : (p.1 == id) with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hb) hn
      rw [if_neg hn, hb]
      rfl
  | true =>
      have hy : p.1 = id := of_decide_eq_true hpid
      rw [if_pos hy, hy, beq_iff_eq.mpr (rfl : id = id)]
      rfl

/-- **Settling a pending read is `Agent.resolve` through its capability.** The
hypothesis is needed: `settleReadCell` is unguarded (its docstring says so),
so on a read that has already settled the readable overwrites the cell and
records a second settlement while the agent's resolve is inert
(`rView_settleRead_unguarded` below). DB-04 M2. -/
theorem rView_settleRead_ok {α ε body : Type} (s : Readable.State α ε) (id : Nat)
    (x : Readable.ReadResult α)
    (hp : (s.readPromises.find? (fun p => p.1 == id)).map Prod.snd = some .pending) :
    rView (body := body) (settleReadTraced s id (.ok x)) =
      Agent.resolve (rView (body := body) s) (capOf (readAddr id)) (.read x) := by
  cases hf : s.readPromises.find? (fun p => p.1 == id) with
  | none => rw [hf] at hp; cases hp
  | some e =>
      rw [hf] at hp
      have hst : e.2 = .pending := Option.some.inj hp
      have he1 : e.1 = id := beq_iff_eq.mp
        (List.find?_some (p := fun (p : Nat × Readable.PromiseState (Readable.ReadResult α) ε) =>
          p.1 == id) hf)
      have hcell : (rCells s).find? (fun e => e.1 == readAddr id) = some (readAddr id, .pending) := by
        rw [find_rCells, hf]
        show some (readAddr e.1, stateMap CellValue.read e.2) = _
        rw [he1, hst]; rfl
      have hfind : (rView (body := body) s).functions.find?
          (fun f => f.resolve == (capOf (readAddr id)).resolve) =
          some (fnOf (readAddr id, (Promise.State.pending :
            Promise.State (CellValue α) (Boundary.Exception ε)))) := by
        show List.find? _ ((rCells s).map fnOf) = _
        rw [List.find?_map]
        have : ((fun (f : Promise.ResolvingFunctions) => f.resolve == (capOf (readAddr id)).resolve) ∘
            fnOf) = (fun (e : Nat × Promise.State (CellValue α) (Boundary.Exception ε)) =>
              e.1 == readAddr id) := by
          funext e; exact two_mul_beq e.1 (readAddr id)
        rw [this, hcell]
        rfl
      have hprom : (fnOf (readAddr id, (Promise.State.pending :
          Promise.State (CellValue α) (Boundary.Exception ε)))).promise = readAddr id := rfl
      rw [Agent.resolve_eq, Agent.callFunctions_fresh _ _ _ _ hfind rfl, Agent.settle_eq, hprom]
      have hpend : Promise.Table.isPending (rView (body := body) s).table (readAddr id) = true := by
        rw [Promise.Table.isPending_iff]
        show Option.map Promise.Cell.state (Option.map Prod.snd (List.find? (fun e => e.1 == readAddr id)
          ((rCells s).map (fun e => (e.1, Promise.Cell.mk e.2 (handledAt s e.1)))))) = _
        rw [List.find?_map]
        have : ((fun (e : Nat × Promise.Cell (CellValue α) (Boundary.Exception ε)) =>
            e.1 == readAddr id) ∘ (fun e => (e.1, Promise.Cell.mk e.2 (handledAt s e.1)))) =
            (fun (e : Nat × Promise.State (CellValue α) (Boundary.Exception ε)) =>
              e.1 == readAddr id) := rfl
        rw [this, hcell]
        rfl
      unfold Promise.Table.settleAndTrigger Promise.Table.settleTraced Promise.Table.settle
      rw [hpend]
      simp only [if_true]
      show Agent.Agent.mk _ _ _ _ _ _ _ _ _ = Agent.Agent.mk _ _ _ _ _ _ _ _ _
      have hcells := rCells_settleRead s id x
      congr 1
      · -- the table
        show Promise.Table.mk (List.map (fun e => (e.1, Promise.Cell.mk e.2 (handledAt s e.1)))
            (rCells (settleReadTraced s id (.ok x)))) (s.nextRead + 1) =
          Promise.Table.mk (List.map _ (List.map (fun e => (e.1, Promise.Cell.mk e.2 (handledAt s e.1)))
            (rCells s))) (s.nextRead + 1)
        rw [hcells, List.map_map, List.map_map]
        congr 1
        apply List.map_congr_left
        intro e _
        show (_ : Nat × Promise.Cell (CellValue α) (Boundary.Exception ε)) =
          (if (e.1 == readAddr id) = true then _ else _)
        cases hb : (e.1 == readAddr id) with
        | false => rw [Function.comp_apply]; dsimp only; rw [hb]; rfl
        | true => rw [Function.comp_apply]; dsimp only; rw [hb]; rfl
      · -- the functions
        show List.map fnOf (rCells (settleReadTraced s id (.ok x))) =
          List.map _ (List.map fnOf (rCells s))
        rw [hcells, List.map_map, List.map_map]
        apply List.map_congr_left
        intro e _
        obtain ⟨k, st⟩ := e
        show fnOf (if (k == readAddr id) = true then _ else (k, st)) =
          (if (2 * k == 2 * readAddr id) = true then _ else _)
        rw [two_mul_beq]
        cases hb : (k == readAddr id) with
        | false => rfl
        | true =>
            have hk : k = readAddr id := beq_iff_eq.mp hb
            subst hk
            rfl
      · -- the settlement trace
        show List.map settlementOf (List.filterMap _ (s.trace ++ [.settled (.read id (.ok x))])) = _
        rw [List.filterMap_append, List.map_append]
        rfl

/-! ## Refuted without the pending hypothesis -/

/-- Default algorithms. -/
def alg0 : Readable.Algorithms := ⟨.one, 0, 0⟩

/-- A readable state whose read `0` has already settled `done`. -/
def settledRead : Readable.State Unit Unit :=
  (Readable.freshReadCell (Readable.initial alg0 .posInfinity) (.fulfilled .done)).1

/-- **Refuted (expected to hold without a hypothesis, as the writable square
does).** On a read that has already settled, the readable's unguarded
`settleReadCell` with its trace event records a second settlement, while the
agent's `resolve` is inert. DB-04 M2. -/
theorem rView_settleRead_unguarded :
    rView (body := Unit) (settleReadTraced settledRead 0 (.ok .done)) ≠
      Agent.resolve (rView (body := Unit) settledRead) (capOf (readAddr 0)) (.read .done) := by
  intro h
  have hl := congrArg (fun a => a.settlements.length) h
  have h10 : (1 : Nat) = 0 := hl
  exact absurd h10 (by decide)

end W8bRead
```

### A.3 `W8bTransform.lean`

The refutation `reactions_cursor_decreases`.

```lean
import Whatwg.Streams.Transform.Laws

/-!
# W8b prototype: the transform's positional reaction view is not a reaction store

Scratch only. `Transform.reactions` folds `Reactions.add` over the current
subscription list, so its identities are positions and its cursor is the list's
length. `Transform.settle` removes the settled promise's subscriptions, so the
cursor of the view goes down: the view cannot be the `reactions` field of an
agent view that `Agent.Le` orders (`Le.reactionsNext`), and a reaction's
identity changes when an earlier one is removed.
-/

namespace W8bTrans

open Whatwg.Streams

/-- Native port names. -/
def ports0 : Transform.Ports := ⟨0, 1, 2, 3, 4⟩

/-- Foreign algorithm names. -/
def alg0 : Transform.Algorithms := ⟨5, 6, 7⟩

/-- The count-profile initial transform with one transform-reaction
subscription on its pending backpressure promise. -/
def subscribed : Transform.State Unit Unit Unit :=
  let s := Transform.initial (α := Unit) (β := Unit) (ε := Unit) (.finite 1) (.finite 1) .one
    ports0 alg0 0 0
  { s with subscriptions := [.reaction s.backpressurePromise (.transform 0)] }

/-- **Refuted (expected to hold).** Settling the subscribed promise lowers the
positional view's registration cursor from `1` to `0`. -/
theorem reactions_cursor_decreases :
    ∃ t, Transform.settle subscribed subscribed.backpressurePromise .fulfilled = some t ∧
      (Transform.reactions t).next < (Transform.reactions subscribed).next :=
  ⟨_, rfl, by decide⟩

end W8bTrans
```

### A.4 `W8bStepProbe.lean`

The writable and readable step bridges evaluated on concrete runs; `#eval` output: `(21, true)`, `(27, true)`, `(14, true)`, `(25, true)`; operation counts `[(5, 6, 0, 0), (2, 0, 1, 1), (3, 3, 0, 0), (4, 0, 5, 2)]`; `(13, true)`, `(5, true)`; `[(4, 5, 0, 0), (3, 0, 4, 1)]`; without step 7 `[true, true, false, true]`.

```lean
import Whatwg.Streams.Writable.Laws
import Whatwg.Streams.Readable.Laws
import Whatwg.Ecma262.AgentLaws

/-!
# W8b probe: the step-level bridge evaluated on concrete runs

Scratch only; `#eval` is used because this file is not in the audited tree.
For every consecutive pair `(s, t)` of a run, the probe compares the view of
`t` with the agent the store operations of the step reach from the view of
`s`: the allocations the cursor moved over, then the settlements the trace
gained, in trace order, then the identities newly marked handled. The views
are restated from `W8bWritable.lean` and `W8bReadable.lean`.
-/

namespace W8bProbe

open Whatwg.Streams Whatwg.Ecma262
open Whatwg.Ecma262.Agent (instDecidableEqExcept)

def capOf (id : Nat) : Promise.Capability := ⟨id, 2 * id, 2 * id + 1⟩

def fnOf {v r : Type} (e : Nat × Promise.State v r) : Promise.ResolvingFunctions :=
  ⟨e.1, 2 * e.1, 2 * e.1 + 1, match e.2 with | .pending => false | _ => true⟩

/-! ## Writable -/

def wView {α ε body : Type} (s : Writable.State α ε) :
    Agent.Agent Unit (Boundary.Exception ε) body :=
  ⟨Writable.promiseTable s, Promise.Reactions.empty, [], Jobs.Queue.empty,
    s.promises.map fnOf, 2 * s.nextPromise, .checkpoint, none,
    Writable.settlementTrace s⟩

def settleOp {ε body : Type} :
    Nat × Except (Boundary.Exception ε) Unit → Agent.Op Unit (Boundary.Exception ε) body
  | (id, .ok ()) => .resolve (capOf id) ()
  | (id, .error e) => .reject (capOf id) e

/-- The store operations of a writable step, in the order the bridge uses. -/
def wStoreOps {α ε body : Type} (s t : Writable.State α ε) :
    List (Agent.Op Unit (Boundary.Exception ε) body) :=
  List.replicate (t.nextPromise - s.nextPromise) .newPromise ++
    ((Writable.settlementTrace t).drop (Writable.settlementTrace s).length).map settleOp ++
    (t.handled.drop s.handled.length).map .markHandled

def wCheck (s t : Writable.State Unit Unit) : Bool :=
  decide (wView (body := Unit) t = (Agent.runOps (wView (body := Unit) s) (wStoreOps s t)).1)

/-- Run a tape: tick to quiescence (bounded), then admit the next decision. -/
def wDrive : Nat → Writable.State Unit Unit → List (Writable.Decision Unit Unit) →
    List (Writable.State Unit Unit)
  | 0, s, _ => [s]
  | fuel + 1, s, ds =>
      match Writable.tick s with
      | some t => s :: wDrive fuel t ds
      | none =>
          match ds with
          | [] => [s]
          | d :: rest =>
              match Writable.decide s d with
              | some t => s :: wDrive fuel t rest
              | none => [s]

def pairs {β : Type} : List β → List (β × β)
  | a :: b :: rest => (a, b) :: pairs (b :: rest)
  | _ => []

def algF : Writable.Algorithms := ⟨some .one, some .fulfilled, some .fulfilled, some .fulfilled⟩
def algX : Writable.Algorithms := ⟨some .one, some (.foreign 7), some (.foreign 8), some (.foreign 9)⟩

/-- Default sinks, high-water mark 1: two writes and a close. -/
def runW1 : List (Writable.State Unit Unit) :=
  wDrive 200 (Writable.initial (.finite 1) algF 0 0)
    [.write (), .queryReady, .write (), .close, .queryClosed]

/-- Positive infinite high-water mark: the ready promise starts fulfilled. -/
def runW4 : List (Writable.State Unit Unit) :=
  wDrive 200 (Writable.initial .posInfinity algX 2 0)
    [.write (), .returnSink (.settled (.rejected (.typeError 11))), .write (), .close]

#eval (runW4.length, (pairs runW4).all (fun p => wCheck p.1 p.2))

/-- Foreign sinks at seed 5: a write whose sink returns pending, then a
controller error, then an abort: rejections, handled marks and the erroring
path. -/
def runW2 : List (Writable.State Unit Unit) :=
  wDrive 200 (Writable.initial (.finite 1) algX 5 0)
    [.write (), .returnSink .pending, .controllerError (.typeError 40), .abort (.typeError 41),
     .returnSink .pending, .queryClosed]

/-- High-water mark zero: the ready promise starts pending. -/
def runW3 : List (Writable.State Unit Unit) :=
  wDrive 200 (Writable.initial (.finite 0) algF 0 0)
    [.write (), .write (), .abort (.typeError 3), .close]

#eval (runW1.length, (pairs runW1).all (fun p => wCheck p.1 p.2))
#eval (runW2.length, (pairs runW2).all (fun p => wCheck p.1 p.2))
#eval (runW3.length, (pairs runW3).all (fun p => wCheck p.1 p.2))
#eval ((pairs runW1 ++ pairs runW2 ++ pairs runW3).filter (fun p => wStoreOps (body := Unit) p.1 p.2 ≠ [])).length

/-- How many operations of each kind the runs exercise: allocations,
fulfilments, rejections, handled marks. -/
def opKinds {v r b : Type} (ops : List (Agent.Op v r b)) : Nat × Nat × Nat × Nat :=
  ops.foldl (fun acc op => match op with
    | .newPromise => (acc.1 + 1, acc.2.1, acc.2.2.1, acc.2.2.2)
    | .resolve _ _ => (acc.1, acc.2.1 + 1, acc.2.2.1, acc.2.2.2)
    | .reject _ _ => (acc.1, acc.2.1, acc.2.2.1 + 1, acc.2.2.2)
    | .markHandled _ => (acc.1, acc.2.1, acc.2.2.1, acc.2.2.2 + 1)
    | _ => acc) (0, 0, 0, 0)

#eval [runW1, runW2, runW3, runW4].map (fun run =>
  opKinds ((pairs run).flatMap (fun p => wStoreOps (body := Unit) p.1 p.2)))
#eval [runW1, runW2, runW3, runW4].map (fun run => (run.getLast?.map (fun s => s.status)).isSome)

/-! ## Readable -/

inductive CellValue (α : Type) where
  | unit
  | read (r : Readable.ReadResult α)
  deriving DecidableEq, Repr

def stateMap {v w r : Type} (f : v → w) : Promise.State v r → Promise.State w r
  | .pending => .pending
  | .fulfilled x => .fulfilled (f x)
  | .rejected e => .rejected e

def readAddr (k : Nat) : Nat := k + 1

def rCells {α ε : Type} (s : Readable.State α ε) :
    List (Nat × Promise.State (CellValue α) (Boundary.Exception ε)) :=
  (0, stateMap (fun _ => CellValue.unit) s.closedPromise) ::
    s.readPromises.map (fun p => (readAddr p.1, stateMap CellValue.read p.2))

def handledAt {α ε : Type} (s : Readable.State α ε) (id : Nat) : Bool :=
  match id, s.status with
  | 0, .errored _ => true
  | _, _ => false

def settlementOf {α ε : Type} :
    Readable.Settlement α ε → Nat × Except (Boundary.Exception ε) (CellValue α)
  | .closed r => (0, r.map (fun _ => CellValue.unit))
  | .read id r => (readAddr id, r.map CellValue.read)

def rView {α ε body : Type} (s : Readable.State α ε) :
    Agent.Agent (CellValue α) (Boundary.Exception ε) body :=
  ⟨⟨(rCells s).map (fun e => (e.1, Promise.Cell.mk e.2 (handledAt s e.1))), s.nextRead + 1⟩,
    Promise.Reactions.empty, [], Jobs.Queue.empty, (rCells s).map fnOf, 2 * (s.nextRead + 1),
    .checkpoint, none, (Readable.settlementTrace s).map settlementOf⟩

def rSettleOp {α ε body : Type} :
    Nat × Except (Boundary.Exception ε) (CellValue α) → Agent.Op (CellValue α) (Boundary.Exception ε) body
  | (id, .ok v) => .resolve (capOf id) v
  | (id, .error e) => .reject (capOf id) e

/-- The store operations of a readable step: allocations, settlements in trace
order, and `ReadableStreamError` step 7 when the step errors the stream. -/
def rStoreOps {α ε body : Type} (s t : Readable.State α ε) :
    List (Agent.Op (CellValue α) (Boundary.Exception ε) body) :=
  List.replicate (t.nextRead - s.nextRead) .newPromise ++
    (((Readable.settlementTrace t).drop (Readable.settlementTrace s).length).map settlementOf).map
      rSettleOp ++
    (if handledAt t 0 && !handledAt s 0 then [.markHandled 0] else [])

def rCheck (s t : Readable.State Unit Unit) : Bool :=
  decide (rView (body := Unit) t = (Agent.runOps (rView (body := Unit) s) (rStoreOps s t)).1)

/-- External decisions, then the pull job whenever one is queued. -/
def rDrive : Nat → Readable.State Unit Unit → List (Readable.Decision Unit Unit) →
    List (Readable.State Unit Unit)
  | 0, s, _ => [s]
  | fuel + 1, s, ds =>
      match Readable.runPullJob s with
      | some t => s :: rDrive fuel t ds
      | none =>
          match ds with
          | [] => [s]
          | d :: rest =>
              match Readable.step s d with
              | some t => s :: rDrive fuel t rest
              | none => [s]

def ralg : Readable.Algorithms := ⟨.one, 0, 0⟩

/-- Reads before and after enqueues, a pull answered, a close with a pending
read, and a read after close. -/
def runR1 : List (Readable.State Unit Unit) :=
  rDrive 200 (Readable.initial ralg (.finite 1))
    [.read, .pullReturn .pending, .enqueue (), .pull .fulfilled, .read, .read,
     .pullReturn (.settled .fulfilled), .enqueue (), .close, .read]

/-- An error with pending reads, then a read on the errored stream. -/
def runR2 : List (Readable.State Unit Unit) :=
  rDrive 200 (Readable.initial ralg (.finite 0))
    [.read, .read, .error (.typeError 9), .read]

#eval (runR1.length, (pairs runR1).all (fun p => rCheck p.1 p.2))
#eval (runR2.length, (pairs runR2).all (fun p => rCheck p.1 p.2))
#eval ((pairs runR1 ++ pairs runR2).filter (fun p => rStoreOps (body := Unit) p.1 p.2 ≠ [])).length
#eval [runR1, runR2].map (fun run =>
  opKinds ((pairs run).flatMap (fun p => rStoreOps (body := Unit) p.1 p.2)))

/-! ## The same check without step 7: the error step disagrees -/

def rStoreOpsNo7 {α ε body : Type} (s t : Readable.State α ε) :
    List (Agent.Op (CellValue α) (Boundary.Exception ε) body) :=
  List.replicate (t.nextRead - s.nextRead) .newPromise ++
    (((Readable.settlementTrace t).drop (Readable.settlementTrace s).length).map settlementOf).map
      rSettleOp

#eval (pairs runR2).map (fun p =>
  decide (rView (body := Unit) p.2 = (Agent.runOps (rView (body := Unit) p.1) (rStoreOpsNo7 p.1 p.2)).1))

end W8bProbe
```

### A.5 `W8bConfigProbe.lean`

The configuration view and its step bridge evaluated on three runs; `#eval` output: 45, 8 and 19 pairs all `true`; operation counts `[[5, 6, 0, 4, 0, 4, 4, 5, 6], [1, 0, 0, 3, 0, 0, 0, 0, 0], [1, 0, 2, 3, 2, 3, 3, 1, 2]]` (allocations, fulfilments, rejections, registrations, handled marks, job starts, job finishes, script entries, script exits); largest queue `[1, 1, 2]`; without THEN step 12 `[false, false, false]`; with Q4's `reactions` `[false, false, false]`.

```lean
import Whatwg.Streams.Semantics.Step
import Whatwg.Ecma262.AgentLaws

/-!
# W8b probe: the configuration viewed as one agent, observer jobs in the queue

Scratch only; `#eval` is used because this file is not in the audited tree.
The view is the writable store view of `W8bWritable.lean` extended with the
configuration's registrations as reactions and its observer tokens as the
agent's queue, keyed by registration identity, with no job-serial supply.

- A registration made while its promise was pending is in both reaction
  lists (THEN step 9), with the callback as the handler of both, since the
  configuration calls it on either outcome; one made after the promise
  settled is a held record (THEN steps 10 and 11). The trace order of the
  `registered` event and the promise's `settled` event decides which.
- Phases are read from the table: waiting while pending; after settlement
  `.queued id` on the triggered list and `.done` on the other (FULFILL and
  REJECT steps 4 and 5).
- The handled bit of a cell is the writable's or set by a registration
  (THEN step 12, which `Ordering.register` does not perform).
- Observer tokens are the queue, each with its promise's result as argument;
  start and finish tokens and sink tokens are host activations
  (`script`), not queue entries.
-/

namespace W8bCfg

open Whatwg.Streams Whatwg.Ecma262 Whatwg.Streams.Semantics.Ordering
open Whatwg.Ecma262.Agent (instDecidableEqExcept)

def capOf (id : Nat) : Promise.Capability := ⟨id, 2 * id, 2 * id + 1⟩

def fnOf {v r : Type} (e : Nat × Promise.State v r) : Promise.ResolvingFunctions :=
  ⟨e.1, 2 * e.1, 2 * e.1 + 1, match e.2 with | .pending => false | _ => true⟩

abbrev A := Agent.Agent Unit (Boundary.Exception Unit) Nat

def settledPos (c : Config Unit Unit) (p : Nat) : Option Nat :=
  c.trace.findIdx? (fun e => match e with
    | .writable (.settled id _) => id == p
    | _ => false)

def registeredPos (c : Config Unit Unit) (rid : Nat) : Option Nat :=
  c.trace.findIdx? (fun e => match e with
    | .registered id _ _ => id == rid
    | _ => false)

/-- Registered while the promise was pending. -/
def listed (c : Config Unit Unit) (r : Promise.Reaction Nat) : Bool :=
  match Writable.lookupPromise c.writable r.promise with
  | some .pending => true
  | some _ =>
      match settledPos c r.promise, registeredPos c r.id with
      | some sp, some rp => decide (rp < sp)
      | _, _ => false
  | none => false

def phaseFor (c : Config Unit Unit) (r : Promise.Reaction Nat) (k : Promise.ReactionType) :
    Promise.ReactionPhase :=
  match Writable.lookupPromise c.writable r.promise, k with
  | some (.fulfilled _), .fulfill => .queued r.id
  | some (.rejected _), .reject => .queued r.id
  | some .pending, _ => .waiting
  | _, _ => .done

def asListed (c : Config Unit Unit) (k : Promise.ReactionType) (r : Promise.Reaction Nat) :
    Promise.Reaction Nat :=
  ⟨r.id, r.promise, k, r.handler, none, phaseFor c r k⟩

def asHeld (c : Config Unit Unit) (r : Promise.Reaction Nat) : Promise.Reaction Nat :=
  ⟨r.id, r.promise,
    (match Writable.lookupPromise c.writable r.promise with
      | some (.rejected _) => .reject | _ => .fulfill),
    r.handler, none, .queued r.id⟩

def argOf (c : Config Unit Unit) (rid : Nat) : Option (Except (Boundary.Exception Unit) Unit) :=
  match c.registrations.find? (fun r => r.id == rid) with
  | none => none
  | some r =>
      match Writable.lookupPromise c.writable r.promise with
      | some (.fulfilled _) => some (.ok ())
      | some (.rejected e) => some (.error e)
      | _ => none

def jobOf (c : Config Unit Unit) (j : Job) : Option (Agent.Job Unit (Boundary.Exception Unit)) :=
  match j.kind with
  | .observer rid => (argOf c rid).map (fun a => ⟨rid, a⟩)
  | _ => none

def handledCell (c : Config Unit Unit) (p : Nat) : Bool :=
  decide (p ∈ c.writable.handled) || c.registrations.any (fun r => r.promise == p)

def cView (c : Config Unit Unit) : A :=
  { table := ⟨c.writable.promises.map (fun p => (p.1, Promise.Cell.mk p.2 (handledCell c p.1))),
      c.writable.nextPromise⟩,
    reactions := ⟨(c.registrations.filter (listed c)).map (asListed c .fulfill),
      (c.registrations.filter (listed c)).map (asListed c .reject), c.nextObserver⟩,
    held := (c.registrations.filter (fun r => !listed c r)).map (asHeld c),
    queue := ⟨c.jobs.filterMap (jobOf c)⟩,
    functions := c.writable.promises.map fnOf,
    nextFunction := 2 * c.writable.nextPromise,
    active := (match c.active with
      | .checkpoint => .checkpoint
      | .script => .script
      | .intrinsic _ => .script
      | .observer j => match j.kind with
          | .observer rid => .job rid
          | _ => .script),
    running := (match c.active with
      | .observer j => jobOf c j
      | _ => none),
    settlements := Writable.settlementTrace c.writable }

def settleOp : Nat × Except (Boundary.Exception Unit) Unit → Agent.Op Unit (Boundary.Exception Unit) Nat
  | (id, .ok ()) => .resolve (capOf id) ()
  | (id, .error e) => .reject (capOf id) e

/-- The agent operations of one configuration step: the writable's store
operations, then the registration the step made, then the activation change. -/
def cOps (c t : Config Unit Unit) : List (Agent.Op Unit (Boundary.Exception Unit) Nat) :=
  List.replicate (t.writable.nextPromise - c.writable.nextPromise) .newPromise ++
    ((Writable.settlementTrace t.writable).drop (Writable.settlementTrace c.writable).length).map
      settleOp ++
    (t.writable.handled.drop c.writable.handled.length).map .markHandled ++
    (t.registrations.drop c.registrations.length).map
      (fun r => .perform r.promise r.handler r.handler false) ++
    (match c.active, t.active with
      | .checkpoint, .observer _ => [.startJob]
      | .observer _, .checkpoint => [.finishJob (.ok ())]
      | .checkpoint, .script => [.enterScript]
      | .checkpoint, .intrinsic _ => [.enterScript]
      | .script, .checkpoint => [.leaveScript]
      | .intrinsic _, .checkpoint => [.leaveScript]
      | _, _ => [])

def cCheck (c t : Config Unit Unit) : Bool :=
  decide (cView t = (Agent.runOps (cView c) (cOps c t)).1)

/-- Tick to quiescence, then try decisions in order, skipping refused ones. -/
def cDrive : Nat → Config Unit Unit → List (Decision Unit Unit) → List (Config Unit Unit)
  | 0, c, _ => [c]
  | fuel + 1, c, ds =>
      match tick c with
      | some t => c :: cDrive fuel t ds
      | none =>
          match ds with
          | [] => [c]
          | d :: rest =>
              match decide c d with
              | some t => c :: cDrive fuel t rest
              | none => cDrive fuel c rest

def pairs {β : Type} : List β → List (β × β)
  | a :: b :: rest => (a, b) :: pairs (b :: rest)
  | _ => []

def algF : Writable.Algorithms := ⟨some .one, some .fulfilled, some .fulfilled, some .fulfilled⟩
def algX : Writable.Algorithms := ⟨some .one, some (.foreign 7), some (.foreign 8), some (.foreign 9)⟩

def obs (cell cb : Nat) : Decision Unit Unit := .observe ⟨0, cell⟩ cb

/-- Observers on the ready and closed promises before start, writes, a close,
observer returns and script re-entries. -/
def run1 : List (Config Unit Unit) :=
  cDrive 400 (initial 0 (.finite 1) algF 0 0)
    [obs 0 10, obs 1 11, .writable (.write ()), .scriptReturn, .observerReturn, .scriptBegin,
     obs 2 12, .writable (.write ()), .writable .close, .scriptReturn, .observerReturn,
     .observerReturn, .observerReturn, .scriptBegin, obs 0 13, .scriptReturn, .observerReturn]

/-- Foreign sinks with a rejected write: rejections reach observers. -/
def run2 : List (Config Unit Unit) :=
  cDrive 400 (initial 0 .posInfinity algX 0 0)
    [obs 1 20, .writable (.write ()), .scriptReturn, .writable (.returnSink .pending),
     .writable (.answer .write 2 (.rejected (.typeError 5))), .observerReturn, .observerReturn,
     .scriptBegin, obs 1 21, obs 0 22, .scriptReturn, .observerReturn, .observerReturn]

/-- Two observers on the closed promise and one on the ready promise, which
`initial` stores already fulfilled (a held record); a controller error then
rejects the closed promise, which queues two observer jobs with the reason. -/
def run3 : List (Config Unit Unit) :=
  cDrive 400 (initial 0 (.finite 1) algF 0 0)
    [obs 1 30, obs 1 31, obs 0 32, .scriptReturn, .observerReturn, .scriptBegin,
     .writable (.controllerError (.typeError 6)), .scriptReturn, .observerReturn,
     .observerReturn, .observerReturn]

#eval (run1.length, (pairs run1).map (fun p => cCheck p.1 p.2))
#eval (run2.length, (pairs run2).map (fun p => cCheck p.1 p.2))
#eval (run3.length, (pairs run3).map (fun p => cCheck p.1 p.2))

def opKinds (ops : List (Agent.Op Unit (Boundary.Exception Unit) Nat)) : List Nat :=
  ops.foldl (fun acc op => match op with
    | .newPromise => acc.modify 0 (· + 1)
    | .resolve _ _ => acc.modify 1 (· + 1)
    | .reject _ _ => acc.modify 2 (· + 1)
    | .perform _ _ _ _ => acc.modify 3 (· + 1)
    | .markHandled _ => acc.modify 4 (· + 1)
    | .startJob => acc.modify 5 (· + 1)
    | .finishJob _ => acc.modify 6 (· + 1)
    | .enterScript => acc.modify 7 (· + 1)
    | .leaveScript => acc.modify 8 (· + 1)) [0, 0, 0, 0, 0, 0, 0, 0, 0]

#eval [run1, run2, run3].map (fun run => opKinds ((pairs run).flatMap (fun p => cOps p.1 p.2)))
#eval [run1, run2, run3].map (fun run => (run.map (fun c => (cView c).queue.pending.length)).foldl max 0)

/-- The same check with the configuration's handled bits only (no THEN step
12): registrations then disagree with `perform`, which marks handled. -/
def cViewNo12 (c : Config Unit Unit) : A :=
  { cView c with table := Writable.promiseTable c.writable }

#eval [run1, run2, run3].map (fun run => (pairs run).map (fun p =>
  decide (cViewNo12 p.2 = (Agent.runOps (cViewNo12 p.1) (cOps p.1 p.2)).1)) |>.all id)

/-- The same check with the frozen Q4 view `Ordering.reactions` as the agent's
reactions and no held records: every registration in both lists, the reject
list handler-free, phases copied from the configuration. -/
def cViewQ4 (c : Config Unit Unit) : A :=
  { cView c with reactions := reactions c, held := [] }

#eval [run1, run2, run3].map (fun run => (pairs run).map (fun p =>
  decide (cViewQ4 p.2 = (Agent.runOps (cViewQ4 p.1) (cOps p.1 p.2)).1)) |>.all id)

end W8bCfg
```

### A.6 `AxiomFooter.lean.txt`

The axiom receipt appended to A.1 to A.3 (with the namespace substituted); its output is in section 2.1.

```lean

/-! ## Axiom receipt (scratch only): `Lean.collectAxioms` over every constant this file adds -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := (env.constants.map₂.toList.map Prod.fst).filter fun n => (`W8bProto).isPrefixOf n
  let mut union : Array Name := #[]
  let mut choice : Array Name := #[]
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    for a in axs do
      unless union.contains a do union := union.push a
    if axs.contains ``Classical.choice then choice := choice.push n
  logInfo m!"W8bProto: {names.length} constants; axioms reached (union): {union.toList}; reaching Classical.choice: {choice.toList}"
```

### A.7 `scan_ascriptions.py`

The ascription scan of section 2.2.

```python
"""Count frozen ascription blocks that name store fields and store operations.

A block is a line starting (after indentation) with `#check (@` or
`#whatwg_freeze (@`, joined with every following line that is indented and is
not itself a new command, a docstring opener, or blank. `--` line comments and
`/- -/` block comments inside a block are removed before matching. A name
matches as a whole identifier component: not preceded or followed by an
identifier character, so `s.readPromises`, `State.readPromises` and
`readPromises :=` all match and `readPromisesX` does not.

Usage: python scan_ascriptions.py <repo-root>
"""
import os
import re
import sys
from collections import defaultdict

ROOT = sys.argv[1] if len(sys.argv) > 1 else "."
TEST = os.path.join(ROOT, "WhatwgTest")
NOSTRIP = os.environ.get("NOSTRIP") == "1"

START = re.compile(r"^\s*#(check|whatwg_freeze) \(@")
NEWCMD = re.compile(r"^\s*(#|/--|/-!|theorem |def |example|open |namespace |end |section |variable |set_option |attribute )")

NAMES = {
    # Readable
    "Readable": ["readPromises", "nextRead", "closedPromise", "readRequests", "jobs",
                  "pullAwaiting", "frames", "freshReadCell", "settleReadCell",
                  "settleReadCells", "readTable", "jobQueue", "settlementTrace",
                  "runPullJob", "acceptPullAnswer", "reactPull", "returnPull"],
    # Writable
    "Writable": ["promises", "handled", "nextPromise", "readyPromise", "closedPromise",
                  "writeRequests", "jobs", "control", "lookupPromise", "freshPromise",
                  "settle", "markHandled", "promiseTable", "jobQueue", "settlementTrace",
                  "acceptAnswer", "attachSink"],
    # Transform
    "Transform": ["backpressurePromise", "internalPromises", "subscriptions", "jobs",
                   "lookupPromise", "freshInternal", "subscribe", "notify", "settle",
                   "reactions", "jobQueue", "runJob"],
    # Piping
    "Piping": ["abortPromise", "lookupPromise", "promiseTable", "allWrittenSettled"],
    # Configuration
    "Semantics": ["registrations", "nextObserver", "jobs", "nextJob", "active", "owner",
                   "lookup", "register", "notifySettled", "enqueueJob", "reactions",
                   "jobQueue", "lookupRegistration", "setRegistrationPhase", "activeErase",
                   "phaseErase", "reactionErase"],
}
STORE_SET = sorted({n for v in NAMES.values() for n in v})
MK = ["State.mk", "Config.mk"]


def strip_comments(text):
    if NOSTRIP:
        return text
    text = re.sub(r"/-(?!-|!).*?-/", " ", text, flags=re.S)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def blocks(path):
    with open(path, encoding="utf-8") as f:
        lines = f.read().splitlines()
    i = 0
    while i < len(lines):
        if START.match(lines[i]):
            indent = len(lines[i]) - len(lines[i].lstrip())
            j = i + 1
            while j < len(lines):
                ln = lines[j]
                if ln.strip() == "":
                    break
                if NEWCMD.match(ln):
                    break
                if len(ln) - len(ln.lstrip()) <= indent:
                    break
                j += 1
            yield i + 1, strip_comments("\n".join(lines[i:j]))
            i = j
        else:
            i += 1


def ident(name):
    return re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])")


PAT = {n: ident(n) for n in STORE_SET + MK}


def calculus_of(rel):
    parts = rel.replace("\\", "/").split("/")
    if len(parts) > 2 and parts[1] == "Streams":
        return parts[2] if parts[2].endswith(".lean") is False else parts[2][:-5]
    return parts[1]


def main():
    per_file = defaultdict(lambda: defaultdict(int))
    any_store = defaultdict(int)
    total_blocks = defaultdict(int)
    mk_hits = []
    all_store_blocks = 0
    for dirpath, _, files in os.walk(TEST):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, ROOT)
            for lineno, text in blocks(path):
                total_blocks[rel] += 1
                hit = False
                for n in STORE_SET:
                    if PAT[n].search(text):
                        per_file[rel][n] += 1
                        hit = True
                for m in MK:
                    if PAT[m].search(text):
                        mk_hits.append((rel, lineno, m))
                if hit:
                    any_store[rel] += 1
                    all_store_blocks += 1
    print("# ascription blocks per file, and blocks naming at least one store name")
    for rel in sorted(total_blocks):
        if any_store[rel]:
            print(f"{total_blocks[rel]:5d} {any_store[rel]:5d}  {rel}")
    print(f"total blocks naming a store name: {all_store_blocks}")
    print()
    print("# per name, per file")
    for n in STORE_SET:
        rows = [(rel, per_file[rel][n]) for rel in sorted(per_file) if per_file[rel][n]]
        if rows:
            tot = sum(c for _, c in rows)
            print(f"{n}: {tot}  " + ", ".join(f"{os.path.basename(r)}={c}" for r, c in rows))
    print()
    print("# State.mk / Config.mk ascriptions")
    for rel, lineno, m in mk_hits:
        print(f"{rel}:{lineno} {m}")


if __name__ == "__main__":
    main()
```

### A.8 `scan_sets.py`

The union counts of section 2.2.

```python
"""Union counts of frozen ascription blocks naming a set of store names.

Block and match rules are those of scan_ascriptions.py. The directory is
WhatwgTest/Streams. Each set is printed with the number of blocks that name at
least one member, and the per-member counts.

Usage: python scan_sets.py <repo-root>
"""
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
import scan_ascriptions as sa  # noqa: E402

ROOT = sys.argv[1]
sa.ROOT = ROOT
DIR = os.path.join(ROOT, "WhatwgTest", "Streams")

SETS = {
    "W8 design's set (fields + 5 accessors)": [
        "readPromises", "nextRead", "promises", "handled", "nextPromise", "jobs",
        "registrations", "nextObserver", "nextJob", "lookupPromise", "freshPromise",
        "jobQueue", "promiseTable", "readTable"],
    "promise fields only": [
        "readPromises", "nextRead", "closedPromise", "promises", "handled", "nextPromise",
        "readyPromise", "backpressurePromise", "internalPromises", "abortPromise"],
    "job and reaction fields only": [
        "jobs", "registrations", "nextObserver", "nextJob", "subscriptions",
        "pullAwaiting", "readRequests", "writeRequests"],
    "existing view functions": [
        "readTable", "promiseTable", "jobQueue", "reactions", "activeErase", "phaseErase",
        "reactionErase"],
    "store operations": [
        "freshReadCell", "settleReadCell", "settleReadCells", "lookupPromise",
        "freshPromise", "settle", "markHandled", "freshInternal", "subscribe", "notify",
        "lookup", "register", "notifySettled", "enqueueJob", "lookupRegistration",
        "setRegistrationPhase"],
}


def main():
    blocks = []
    for dirpath, _, files in os.walk(DIR):
        for fn in files:
            if fn.endswith(".lean"):
                path = os.path.join(dirpath, fn)
                rel = os.path.relpath(path, ROOT)
                for lineno, text in sa.blocks(path):
                    blocks.append((rel, lineno, text))
    print(f"ascription blocks under WhatwgTest/Streams: {len(blocks)}")
    for title, names in SETS.items():
        pats = {n: sa.ident(n) for n in names}
        union = 0
        per = {n: 0 for n in names}
        for _, _, text in blocks:
            hit = False
            for n, p in pats.items():
                if p.search(text):
                    per[n] += 1
                    hit = True
            union += hit
        print(f"\n## {title}: {union} blocks")
        print("  " + ", ".join(f"{n}={c}" for n, c in per.items()))


if __name__ == "__main__":
    main()
```
