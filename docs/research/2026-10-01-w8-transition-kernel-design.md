# W8 design: a generic transition kernel, one promise table, one job queue

Status: design record of the W8 seat of review lane W (rulings R-W0,
R-W1). It recommends a design and leaves every ruling to the coordinator. It
makes no Model Claim, closes no graph edge and changes no disposition. Base
commit: `97a871522ce18f792449f51300c9d93288abb398`. Every prototype named
here was built in this seat's worktree and removed before the last commit;
the branch changes this file only.

Evidence labels follow `docs/research/2026-09-30-implementation-review.md`:
`[C]` measured by this seat, with its command; `[S]` read in source by this
seat; `[H]` a hypothesis not tried.

## 1. Recommendation

Add one module, `Whatwg.Streams.Kernel`, and keep every per-calculus
inductive (Route B, R-P12's "generalize").

- The kernel owns `Kernel.Path step : σ → List L → σ → Prop`, the labelled
  derivations of any one-step relation, with nil, cons, append, single,
  snoc, mono, congr, simulation, invariant and determinism laws; the graph
  and run faces of a partial step and their agreement; and
  `Kernel.stage tick accept` with `Kernel.Exclusive` and the
  fixed-external-word comparability law now proved only for Semantics.
- Each calculus gains `step_iff_stage` and a bridge `… ↔ Kernel.Path Step …`;
  its frozen nil, cons and append lemmas and the two Decision-8 laws become
  corollaries. Measured: build green, no battery touched, no authored type,
  value or kind changed in the fingerprint, 50 authored lines added, no
  elaboration time outside run-to-run noise.
- Route A (each relation an `abbrev` of `Kernel.Path`) also builds green with
  alias theorems, but changes the kind of five relations and ten
  constructors and deletes 45 generated companions. Not additive under
  R-W1(b); it is the fallback.
- Invariants: the queue invariant of the Readable and of the Writable
  machine and registration-identity freshness are proved in the prototype
  through `Kernel.Path.invariant`, with no reachability hypothesis.
  `CellsWellFormed` names a predicate only the held P8a draft states; its
  owner clause holds by representation and the rest is P8's CFG-CELLS.
- Proof style: adopt `fun_cases` (gate-accepted, choice-free, 33 lines to 8
  on one proof); drop `register_simp_attr` (29 gate findings, and R-W1(d)
  forbids the module it needs); keep the four `decide` names; drop typed
  identifiers and the `sizeCalled` reorder.
- Stores: Q3 and Q4 unified carriers and operations through views; storage
  is still per calculus and 178 frozen ascriptions name it. W8b is a view
  onto W9's agent record with bridges, not a field change.

Order: W8a (kernel, bridges, re-proofs, the three proved invariants, the
`find?` cleanup) needs nothing from W9 and follows a breaker packet. W8b
waits for W9's agent record. The three schedulers over one Writable step,
and a Readable machine running its own pull reactions, stay with P8.

## 2. Evidence

### 2.1 Setup

`git switch -c review/w8-kernel-design 97a8715`, the `.lake` cache copied
from the main checkout, then `lake build`: 386 jobs, exit 0, gate line
"checked 222 source files and 16723 declarations", strict ceiling over five
prefixes with 0 exceptions. `[C]`

The fingerprint tool `FingerprintWhatwg.lean` run at the base
(`lake env lean FingerprintWhatwg.lean > fp-base.tsv`) gives 12,766 lines,
identical to the lane V file `fp-final2.tsv` (`Compare-Object`, 0
differences). Every fingerprint comparison below is against `fp-base.tsv`.
`[C]`

### 2.2 The five transition relations (question a)

Read in the five `Step.lean` files under `Whatwg/Streams/` (Readable,
Writable, Transform, Piping, Semantics), the four `Laws.lean` files and
`Semantics/Runs.lean`. `[S]`

| Calculus | One step | Closure | Label | Lemmas over the closure |
| --- | --- | --- | --- | --- |
| Readable | `Step s d t := step s d = some t` | inductive `Steps`, `nil`/`cons` | `Decision α ε` | `steps_nil_iff`, `steps_cons_iff`, `steps_append_iff` (iffs, in `Step.lean`) |
| Writable | `Step s d t := (match d with none => tick s, some a => decide s a) = some t` | inductive `Reaches`, `nil`/`cons` | `Option (Decision α ε)` | `reaches_nil`, `reaches_cons`, `reaches_append_iff` (iffs), `step_deterministic` (in `Laws.lean`) |
| Transform | as Writable, over `Transform.tick`, `decide` | inductive `Reaches`, binders `middle last` | `Option (Decision α β ε)` | `reaches_nil`, `reaches_cons`, `reaches_append` (implications only) |
| Piping | as Writable, over `Piping.tick`, `decide` | inductive `Reaches`, binders `middle last` | `Option (Decision α ε)` | `reaches_nil_iff`, `reaches_cons_iff`, `reaches_append_iff`; invariants `reaches_no_new_read`, `reaches_selection_stable` |
| Semantics | as Writable, over `Ordering.tick`, `decide` | inductive `Reaches`; inductive `EpisodePrefix` (guarded `cons`) | `Option (Decision α ε)` | `reaches_append` (implication), `episodePrefix_reaches`, `step_deterministic`, private `reaches_nil_eq`, `reaches_cons_inv`, and the Decision-8 laws `fixed_external_word_prefix_comparable`, `fixed_external_word_normalized_unique` over a private 65-line `strip` |

Every closure is indexed by start state, label list and end state, with
labels accumulated as a list, and every constructor pair has the same shape.
Where they differ:

1. Readable's label has no silent case, so `Readable.Steps` cannot run its
   own job queue (`runPullJob` is reachable only through `Transform.runJob`).
2. Inversion (`cons_iff`, `nil_iff`) exists for Readable, Writable and
   Piping, privately for Semantics, and not at all for Transform.
3. `step_deterministic` is stated for Writable and Semantics only.
4. No calculus states snoc, single-step or a generic invariant transport;
   Piping and Semantics re-prove invariant transport by induction at each use.
5. Only Semantics has a comparability law; it rests on
   `tick_decide_exclusive`, and the local Writable machine is not exclusive
   (2.6), so the law cannot be transferred to it.
6. Every `Step` is the graph of a partial function. For Readable the graph
   is definitional (`Readable.step_eq_graph : Step = Kernel.Graph step` is
   `rfl`). For the other four it is not: `Step` matches on the label inside
   its body, and the elaborator does not identify that matcher with
   `Kernel.stage`'s at an open label (`rfl` fails; `cases d <;> rfl`
   succeeds). `[C]` probe `StageProbe.lean`. The bridge is therefore a
   pointwise iff, `step_iff_stage`, proved by `cases d <;> exact Iff.rfl`.

### 2.3 Frozen exposure (question b)

Counted over every `#check` ascription block of `WhatwgTest/Streams/**` by a
PowerShell scan that joins each `#check` with its indented continuation lines.
`[C]`

| Battery | Ascriptions naming a closure | of which constructors or recursors |
| --- | ---: | ---: |
| `Readable/DefaultContract.lean` (P4) | 4 | 0 |
| `Writable/DefaultContract.lean` (P5) | 1 | 0 |
| `Writable/DefaultLaws.lean` (P5) | 3 | 0 |
| `Writable/LifecycleContract.lean` (P5) | 2 | 0 |
| `Transform/BackpressureContract.lean` (P6) | 1 | 0 |
| `Transform/BackpressureLaws.lean` (P6) | 6 | 0 |
| `Piping/ShutdownContract.lean` (P7) | 1 | 0 |
| `Piping/ShutdownLaws.lean` (P7) | 7 | 0 |
| `Piping/ShutdownRuns.lean` (P7) | 2 | 0 |
| `Semantics/OrderingContract.lean` (Q4) | 6 | 4 |
| `Semantics/OrderingLaws.lean` (Q4) | 6 | 0 |
| total | 39 | 4 |

The four constructor ascriptions are `Semantics.Ordering.Reaches.nil`,
`Reaches.cons`, `EpisodePrefix.nil` and `EpisodePrefix.cons`. No battery
names a recursor, `casesOn`, `recOn` or `below`. The six relation-type
ascriptions (`Readable.Steps`, four `Reaches`, `EpisodePrefix`) and the five
`Step` ascriptions survive any route that keeps the constant's type. The
remaining 29 are lemma and run-witness statements. No battery proves
anything by `cases` or `induction` on these relations; every such proof is in
production. Production names a constructor explicitly 21 times
(`Reaches.nil`, `Reaches.cons` in `Writable/Lifecycle.lean`,
`Transform/Runs.lean`, `Transform/Laws.lean`, `Piping/Laws.lean`,
`Piping/Runs.lean`). `[C]` `Grep` over the tree.

### 2.4 The routes (question c)

Prototype kernel: `Whatwg/Streams/Kernel.lean`, 334 lines with docstrings
(appendix A). Every theorem in it is axiom-free except `path_graph_iff`,
which uses `propext`. `[C]` `lake env lean KernelAxioms.lean` with one
`#print axioms` per theorem.

**Route B** (inductives kept; bridges; corollary re-proofs), applied to all
five calculi.

| Measure | Result |
| --- | --- |
| `lake build` | 388 jobs, exit 0; gate "checked 223 source files and 16795 declarations", strict ceiling 0 exceptions `[C]` |
| batteries | none edited; all green `[C]` |
| fingerprint, authored lines | 50 added (the kernel and the 13 bridge theorems), 0 changed, 0 removed `[C]` |
| fingerprint, generated lines | 12 changed or removed: the deleted private `strip`, `reaches_nil_eq`, `reaches_cons_inv`, `externalWord_nil_replicate`, `reaches_silent_normalized` of `Semantics/Runs.lean`, `externalWord.eq_1`, and the `_simp` auxiliaries of three re-proved `append` lemmas `[C]` |
| lines, existing files | +124, −174 (`git diff --numstat`); `Semantics/Runs.lean` alone −114 `[C]` |
| lines, new module | +316 at this measurement, 334 with `Path.invariant` and `Path.lift` added later `[C]` |
| choice | 0 strict-ceiling exceptions; the kernel reaches no axiom but `propext` `[C]` |

**Route A** (`abbrev Reaches := Kernel.Path Step`, theorems `Reaches.nil`
and `Reaches.cons` as aliases), applied to Writable, then to Writable and
`Semantics.Ordering.Reaches`, then to all five closures with every `Laws`
and `Runs` proof left as it was.

| Measure | Result |
| --- | --- |
| `lake build` | 388 jobs, exit 0, all three variants; all five: 16745 declarations, 0 exceptions `[C]` |
| batteries | none edited; the frozen `Reaches.nil` and `Reaches.cons` ascriptions of `OrderingContract.lean` accept the alias theorems `[C]` |
| existing proofs | unchanged proofs elaborate: `cases`, `induction`, `.nil`, `.cons` and `apply Reaches.cons` all reach the kernel's constructors through the reducible abbreviation `[C]` |
| fingerprint, Writable | `Reaches` induct to def (type hash unchanged), `Reaches.nil` and `Reaches.cons` ctor to thm (type hashes unchanged), and 9 generated companions removed (`rec`, `recOn`, `casesOn`, `below`, `below.casesOn`, `below.nil`, `below.cons`, `below.rec`, `brecOn`) `[C]` |
| fingerprint, all five | 60 authored lines removed or changed and 15 re-added: five relations induct to def, ten constructors ctor to thm, 45 generated companions gone `[C]` |
| lines, Writable | `Step.lean` +12 −6, `Laws.lean` +3 −15 `[C]` |
| lines, all five, proofs untouched | the five `Step.lean` files, +57 −28 `[C]` |

Route A without the alias theorems breaks the two `Reaches` constructor
ascriptions of `OrderingContract.lean` and the 21 production uses.
`EpisodePrefix` cannot be an `abbrev` of `Kernel.Path` with its frozen
`cons` shape, because its constructor takes the guard and the step as two
hypotheses; it stays inductive under either route. `[S]`

Elaboration time, `Measure-Command { lake env lean <file> }`, seconds,
second of two runs. `[C]` Run-to-run spread on this host is about 0.5 s for
the 10 s file and 0.1 s for the 1 s files.

| File | Base | Route B | Route A (Writable) |
| --- | ---: | ---: | ---: |
| `Whatwg/Streams/Kernel.lean` | — | 0.81 | — |
| `Writable/Step.lean` | 0.77 | 0.77 | 0.80 |
| `Writable/Laws.lean` | 5.96 (first run 5.51) | 5.59 | 5.31 |
| `Writable/Lifecycle.lean` | 1.23 | 1.26 | 1.24 |
| `Readable/Step.lean` | 0.84 | 0.78 | — |
| `Semantics/Runs.lean` | 1.01 | 0.97 | — |
| `Piping/Runs.lean` (R-V5 limit) | 10.89; 10.45 on a later pair | 10.92 | 10.55 (all five) |
| `Transform/Runs.lean` | 2.57 | — | 2.64 (all five) |

**Route C** candidates tried. (i) A typeclass or structure carrying `tick`
and `decide` per calculus adds nothing the bridge iff does not give, and
costs one instance per calculus; not pursued. (ii) The relational face's
function form, `Kernel.path_graph_iff`, lets a run witness be checked by
evaluating `Kernel.run`; the frozen witnesses existentially quantify their
end states and are proved by `repeat first | apply Reaches.cons | … simp`, so
using it means restating them, which is not W8's to do. `[S]`

Recommendation: Route B. It is the only route that is additive in the sense
of R-W1(b), it removes the one large duplicate (`strip`), and it costs one
bridge per calculus.

### 2.5 The smaller duplicates (question d)

| Duplicate | Measured | Reuse mode | Frozen exposure | In W8 |
| --- | --- | --- | --- | --- |
| `exceptDecidableEq` | two private 6-line definitions with `attribute [local instance]`, in `Readable/State.lean` and `Writable/Stream.lean`; core 4.33.1 has no `DecidableEq (Except ε α)` (`Init/Prelude.lean`, `Init/Control/Except.lean`) `[C]` | keep | none by name; moving it changes the value hash of every derived `DecidableEq` instance that captured it | no |
| `Size`, `sizes` | `Readable.Size` and `Writable.Size` are both `abbrev := Data.DyadicSize`; both `sizes` are `def := Data.DyadicSize.sizes`, each with `size_eq` and `sizes_eq` receipts by `rfl` `[S]` | keep: named views of one carrier, by design | the four receipts are frozen and printed by the axiom reports | no |
| `find?` over `map` | nine hand-rolled inductions: four identical `key` lemmas in `Whatwg/Ecma262/Promise.lean`, two in `Writable/Laws.lean` (`lookupPromise_bridge`, `handled_bridge`), two in `Readable/Laws.lean` (`readTable_get` and a settle lemma), one in `Piping/Laws.lean` (`lookup_map_other`) `[C]` | generalize: core `List.find?_map` plus one keyed-update lemma in `Whatwg.Ecma262.Promise` | proof bodies only | yes, W8a, proof-only |
| job-queue views | `jobQueue := Queue.mk s.jobs` in Readable, Writable, Transform and `Semantics.Ordering`, each with a `jobQueue_eq` receipt; dequeue bridges `runPullJob_dequeue_bridge` and `tick_dequeue_bridge` with branch laws re-derived from `Queue.dequeue` `[S]` | already generalize (Q3) | `jobQueue_eq` and the branch laws are frozen | no; W8b |

`List.find?_map` and `Option.map_map` depend on `propext` only. Replacing the
inner induction of `Writable.lookupPromise_bridge` by one `simp only` over
`lookupPromise`, `promiseTable`, `Table.get`, `Table.getCell`, `List.find?_map`,
`Option.map_map` followed by `rfl` elaborates and reaches `propext` and
`Quot.sound`. `[C]` probe `FindMapProbe.lean`. The same replacement in
`handled_bridge` needs `Function.comp_def` first; not finished.

### 2.6 Stores (question e)

What Q3 and Q4 unified `[S]` (`Whatwg/Ecma262/Promise.lean`, `Jobs.lean`,
`docs/PROMISE-EXTRACTION-INVENTORY.md`):

- carriers, by move: `Readable.PromiseState`, `PullAnswer`, `PullReturn` are
  `abbrev`s of `Ecma262.Promise.State`, `Outcome`, `Returned`, and
  `Writable.UnitPromise`, `SinkAnswer`, `SinkReturn` sit on those;
- tables, by generalize: `Writable.promiseTable` and `Readable.readTable` are
  views onto `Ecma262.Promise.Table`, with bridges for lookup, fresh, settle,
  mark-handled and the handled flag; `freshReadCell`, `settleReadCell` and
  `settleReadCells` replace the five inline read-cell updates;
- queues, by generalize: four `jobQueue` views onto `Ecma262.Jobs.Queue`, the
  dequeue bridges, and `Semantics.Ordering.episodePrefix_jobQueue_eq`;
- reactions, by generalize: `Transform.reactions` and
  `Semantics.Ordering.reactions` views onto `Ecma262.Promise.Reactions`.

What is still duplicated is storage: `Readable.State.readPromises` with
`nextRead`; `Writable.State.promises` with `handled` and `nextPromise`; the
job lists of Readable, Writable and Transform; `Config.jobs`,
`registrations`, `nextObserver` and `nextJob`. Each is the canonical field
its calculus reads, and each view is a projection of it.

Frozen exposure of the storage `[C]`: 173 ascriptions in
`WhatwgTest/Streams/**` name one of those fields, `lookupPromise`,
`freshPromise`, `jobQueue`, `promiseTable` or `readTable`, and the frozen
`State.mk` ascriptions of Readable, Writable, Transform and Piping and the
frozen `Config.mk` fix the field lists. Replacing the fields with one store
changes most of these. So the unification W8 can deliver without a frozen
change is a view: a map from each calculus state into W9's agent record, and
bridge theorems that each Streams store operation is the agent operation
under the map.

What W8b needs from W9's `Whatwg.Ecma262.Agent` `[H]`:

1. a table polymorphic in value and reason, or a value universe: Streams
   stores unit promises (Writable) and `ReadResult α` promises (Readable) in
   separate tables today;
2. owner-qualified or otherwise injective keys: Readable and Writable draw
   identities from independent cursors (`nextRead`, `nextPromise`), so one
   table needs keys of the form `Ecma262.Promise.Ref` or a sum, never a
   renumbering, which would change frozen run witnesses that fix ids;
3. a payload-polymorphic job queue whose `DecidableEq` and `Repr` are
   conditional on the payload (`Transform.Job` is `Repr`-only);
4. a run condition the four Streams spellings erase into
   (`frames = []`, `control = []`, Transform's three-way guard, and
   `Ordering.activeErase` onto `Jobs.Active`);
5. if W9 wants a relational face for its step function, the kernel must sit
   below `Whatwg.Ecma262` before its breaker freezes it (decision 2).

### 2.7 Invariants stated and not carried (question f)

`Kernel.Path.invariant` (a property every step keeps holds at the end
of every derivation) carries each of these once the one-step preservation is
proved.

**Queue invariant, Readable.** Proposed and proved in the prototype
`ReadableQueueInv.lean` (about 130 lines, 1.1 s with its import) `[C]`:

```lean
def Readable.QueueInv (s : State α ε) : Prop :=
  Data.Queue.WF sizes s.queue ∧ Data.Queue.SizesAdmissible sizes s.queue
theorem Readable.step_queueInv {s t : State α ε} {d : Decision α ε} :
    QueueInv s → Step s d t → QueueInv t
theorem Readable.steps_queueInv {s t : State α ε} {ds : List (Decision α ε)} :
    Steps s ds t → QueueInv s → QueueInv t
theorem Readable.initial_queueInv (algorithms : Algorithms) (hwm : Size) :
    QueueInv (initial (α := α) (ε := ε) algorithms hwm)
```

It holds as stated, with no reachability hypothesis: the invariant is
inductive. The three queue-changing sites are `error` (`resetQueue`),
`finishEnqueue` (`enqueueValueWithSize`) and `read` (`dequeueValue`, which
needs `DyadicSize.classified`, `ordered` and `exact`); every other operation
keeps the queue. Axioms: `propext`, `Quot.sound`.

**Queue invariant, Writable.** Proposed and proved in the prototype
`WritableQueueInv.lean` (168 lines, 2.2 s with its import) `[C]`:

```lean
def Writable.QueueInv (s : State α ε) : Prop :=
  Data.Queue.WF sizes s.queue ∧ Data.Queue.SizesAdmissible sizes s.queue
theorem Writable.tick_queueInv (s t : State α ε) :
    QueueInv s → tick s = some t → QueueInv t
theorem Writable.decide_queueInv (s t : State α ε) (d : Decision α ε) :
    QueueInv s → decide s d = some t → QueueInv t
theorem Writable.step_queueInv {s t : State α ε} {d : Option (Decision α ε)} :
    QueueInv s → Step s d t → QueueInv t
theorem Writable.reaches_queueInv {s t : State α ε}
    {ds : List (Option (Decision α ε))} :
    Reaches s ds t → QueueInv s → QueueInv t
theorem Writable.initial_queueInv (hwm : Size) (alg : Algorithms)
    (promiseSeed errorSeed : Nat) :
    QueueInv (initial (α := α) (ε := ε) hwm alg promiseSeed errorSeed)
```

It also holds with no reachability hypothesis. `fun_cases tick s` splits the
twenty-branch `tick` into 76 cases (and `decide` into 16), closed by eight
tactic alternatives in six classes: no step, queue untouched, `invokeSink`
(which keeps the queue), growth by
`enqueueValueWithSize` (`enqueueWrite`, `beginClose`), shrinkage by
`dequeueValue` (the close sentinel in `advance`, a fulfilled write
reaction), and reset to `Queue.empty` (`finishErroring`). The local `let`
bindings of `tick` need `simp (config := { zetaDelta := true })`, the form
the tree already uses and V2c's rule 3 admits. Axioms: `propext`,
`Quot.sound`. The prototype's simp lists carry unused arguments that
`warningAsError` would refuse; a builder trims them. Contracts amended:
`readable-default.contract.md`, `writable-default.contract.md`.

**Registration identities.** Proposed and proved in the prototype
`RegistrationsFresh.lean` (about 190 lines, 1.1 s) `[C]`:

```lean
def Ordering.registrationIds (c : Config α ε) : List Nat :=
  c.registrations.map (fun r => r.id)
def Ordering.RegistrationsFresh (c : Config α ε) : Prop :=
  (registrationIds c).Nodup ∧ ∀ i ∈ registrationIds c, i < c.nextObserver
theorem Ordering.step_registrationsFresh {c t : Config α ε} {d : Option (Decision α ε)} :
    RegistrationsFresh c → Step c d t → RegistrationsFresh t
theorem Ordering.reaches_registrationsFresh {c t : Config α ε}
    {ds : List (Option (Decision α ε))} :
    Reaches c ds t → RegistrationsFresh c → RegistrationsFresh t
theorem Ordering.initial_registrationsFresh (owner : Nat) (hwm : Writable.Size)
    (alg : Writable.Algorithms) (promiseSeed errorSeed : Nat) :
    RegistrationsFresh (initial (α := α) (ε := ε) owner hwm alg promiseSeed errorSeed)
theorem Ordering.reachable_registrations_nodup … :
    Reaches (initial owner hwm alg promiseSeed errorSeed) ds c →
      (c.registrations.map (fun r => r.id)).Nodup
```

Freshness alone is not inductive; with the cursor bound it is, so no
reachability hypothesis is needed for the step theorem, and the last theorem
discharges the `hnd` hypothesis of `notifySettled_reactions_bridge` and
`notifySettled_queued_serial` at every configuration reachable from
`initial`. The step proof uses `fun_cases tick c` and `fun_cases decide c d`.
Axioms: `propext`, `Quot.sound`. Contract amended:
`configuration-ordering.contract.md`. The predicate is the first clause of
the P8a draft's `SerialsWellFormed`.

**`CellsWellFormed`.** The dangling reference is the docstring of
`Semantics.Ordering.notifySettled` in
`Whatwg/Streams/Semantics/Configuration.lean`, which says the draft's
owner conjunct "is discharged by `CellsWellFormed`'s registration-owner
clause". The predicate exists only as a row of the
candidate-predicate table in the held P8a draft contract (branch
`codex/configuration-breaker` at `6c44e08`, section "Structural invariants
and general episode statement"); no branch declares it in Lean, and the
landed contract cites "the draft's own `CellsWellFormed`". `[C]` `Grep` over
this tree and the draft's worktree. Debt D38 records the same gap.

In the landed representation the owner clause is discharged by construction:
`Reaction.promise` is a bare cell of the one `Config.owner`, and `register`
admits a registration only after `lookup`, which answers `none` unless
`c.owner = p.owner`. The docstring should say that. The remaining clauses
are a P8 obligation (CFG-CELLS); the statement W8 proposes, elaborated in
`StatementsProbe.lean` `[C]`, is

```lean
def Ordering.CellsWellFormed (c : Config α ε) : Prop :=
  (c.writable.promises.map Prod.fst).Nodup ∧
  (∀ p ∈ c.writable.promises, p.1 < c.writable.nextPromise) ∧
  c.writable.readyPromise ≠ c.writable.closedPromise ∧
  (Writable.lookupPromise c.writable c.writable.readyPromise).isSome ∧
  (Writable.lookupPromise c.writable c.writable.closedPromise).isSome ∧
  ∀ r ∈ c.registrations, (Writable.lookupPromise c.writable r.promise).isSome
```

with preservation `CellsWellFormed c → Step c d t → CellsWellFormed t` and
initialisation at `initial`. Initialisation is proved in the prototype, but
that first proof reaches `Classical.choice`: `simp` closing `seed == seed`,
and `simp` proving `seed ∉ [seed + 1]`, each reach it alone
(`ChoiceProbe.lean`) `[C]`, as `Whatwg/AGENTS.md` warns; a builder names the
lemmas. Preservation is not proved; `[H]` that it is inductive, because the
writable table is append-only and `updateBackpressure` replaces the ready
cell only by a fresh one.

### 2.8 Proof style (question g)

**`register_simp_attr`.** A prototype module `Whatwg/Streams/SimpSetProbe.lean`
with `register_simp_attr streams_run_probe`, imported from
`Whatwg/Streams.lean`. Without `import Lean` the command does not parse.
With it, `lake build` fails at the gate with 29 findings `[C]`: the source
keyword `register_simp_attr`; 12 registered tokens and 12 registered parsers
or syntax kinds (the attribute syntax `streams_run_probe` and
`streams_run_probe_proc`); 2 registered initializers; and 2 bodyless
`opaque` constants (`ext`, `extProc`) that Lean synthesises for the
initializers, which the R-V2 environment rule refuses in every audited
module (the metaprogramming list "relaxes rule 1 and nothing else",
`WhatwgTest/AGENTS.md`). A breaker addendum would have to list a
production module as a metaprogramming module, which R-W1(d) forbids for
`Whatwg/`, and admit synthesised initializer opaques, which reopens a channel
lane V closed; and every Streams module using the set would import `Lean`.
The gain is one named set in place of five local lists. Not worth it.

The local lists measured `[C]`: five `attribute [local simp]` blocks, in
`Piping/Runs.lean`, `Readable/Laws.lean`, `Readable/Reentrancy.lean`,
`Transform/Runs.lean` and `Writable/Lifecycle.lean`, of roughly 18 to 92
names by a whitespace count (the review counted four, of 24 to 85).

**`fun_cases`.** Every `fun_cases` principle of the nine step functions
(`tick` and `decide` of Writable, Transform, Piping and Semantics, and
`Readable.step`) depends on `propext` at most. `[C]` `FunCasesAxioms.lean`.
`Semantics.Ordering.takeSinkHead_canonical_tick`, rewritten in place as
`fun_cases takeSinkHead c token` followed by two closing alternatives, goes
from 33 lines to 8; `Semantics/Step.lean` elaborates in 0.98, 0.93, 0.98 s
against 0.99, 1.03, 1.01 s before; `lake build` passes the gate, which
admits the tactic and the generated principle under the strict prefix
(16809 declarations, 0 exceptions). `[C]` The registration-freshness proof
above uses `fun_cases` on the full `tick` and `decide` of the configuration.
Recommend: use it in every proof W8 touches; leave untouched proofs alone.

**The four `decide` functions** (`Writable/DefaultWriter.lean`,
`Transform/Step.lean`, `Piping/Step.lean`, `Semantics/Step.lean`) shadow
`Decidable.decide` inside their namespaces, which is why that code already
spells `Decidable.decide` in full. 51 frozen ascription or axiom-report
blocks name one of them `[C]`. Renaming breaks those. Declaring them
`protected` changes no fingerprint line (protection is name-resolution state,
not part of the constant) `[H]`, but every short use in production then needs
its namespace: about 137 by a regex count over the Writable, Transform,
Piping and Semantics files `[C]`. Recommend: keep the names; the kernel calls
its parameter `accept`.

Counts re-measured `[C]`: 217 `simp_all`, 271 bare `intros`, 96
`first | rfl | (simp_all …` (114 occurrences of `first | rfl` in any form).

### 2.9 Identifier types and `sizeCalled` (question h)

Readable's `Event.sizeCalled (call algorithm : Nat) (chunk : α)` and
Writable's `Event.sizeCalled (algorithm call : Nat) (chunk : α)` have the same
constructor type, `Nat → Nat → α → Event α ε`; only the binder names and the
meaning differ. The constructor ascriptions survive a swap, but the frozen
`tick` equation of `WhatwgTest/Streams/Writable/DefaultLaws.lean` that emits
`.sizeCalled name call chunk` would assert a different event and fail, and
the producing sites in `Writable/DefaultController.lean` would change. `[C]`
Recommend: drop; record the order in the Writable docstring.

Typed identifiers: 365 of the 1,414 frozen `#check` blocks under
`WhatwgTest/Streams/**` mention `Nat` `[C]`; not every one is an identifier,
but a structure wrapper for promise, call, request and registration ids
changes the types of most. Recommend: drop for the existing calculi; use
`Ecma262.Promise.Ref` and W9's keys in new declarations.

### 2.10 Schedulers (question i)

`Transform.tick`, `Piping.tick` (through `stepWritable`) and
`Semantics.Ordering.tick` each drive `Writable.tick` and `Writable.decide`
and lift the result (`withWritable`, `emit`, `liftWritable`). `[S]` The kernel
does not remove that duplication: what is shared is the inner step, not the
policy, and the three policies differ (a control stack with depth markers;
pipe phases; a checkpoint with a token FIFO). An embedding of Writable
derivations into a scheduler's would be stated with `Kernel.Path.map`, but
none of the three simulates Writable step for step (each refuses or reorders
some steps), so each embedding is its own theorem, and those are P8's
composition obligations.

The local Writable machine is not exclusive: `Writable.not_exclusive :
¬ Kernel.Exclusive (@tick Unit Unit) decide`, proved in `StatementsProbe.lean`
at an empty control stack with one queued sink job, where `tick` runs the job
and `decide` admits `queryReady`. `[C]` That is the reason the configuration
exists, and why the comparability law does not transfer to Writable,
Transform or Piping without a scheduler.

A Readable machine that runs its own pull reactions is
`Kernel.stage (fun s => runPullJob s) step` at no cost in the kernel, but
which reactions may run between which decisions is the global-queue
question of P8 ("promise-job queue in the configuration", `PLAN.md`), not
W8's.

## 3. Public declaration record

Signatures as elaborated (`#check @name` in `Sigs.lean` against the Route B
prototype, `[C]`), shortened by `open Whatwg.Streams`. Roles follow
`Whatwg/AGENTS.md`. Assurance route for every kernel row: local signature
and theorem receipts linked to the laws edge of each graph that consumes the
kernel (decision 3). Spec anchor for every kernel row: none; the module
models no algorithm of `index.bs`, on the precedent of `Semantics/Step.lean`
("Spec anchors: none").

### 3.1 `Whatwg.Streams.Kernel` (new module, W8a)

| Declaration | Signature | Role |
| --- | --- | --- |
| `Kernel.Path` | `{σ : Type u_1} → {L : Type u_2} → (σ → L → σ → Prop) → σ → List L → σ → Prop` | canonical |
| `Kernel.Path.nil` | `∀ … {step} (s : σ), Path step s [] s` | canonical |
| `Kernel.Path.cons` | `∀ … {s mid t : σ} {d : L} {ds : List L}, step s d mid → Path step mid ds t → Path step s (d :: ds) t` | canonical |
| `Kernel.Path.nil_iff` | `Path step s [] t ↔ s = t` | derived |
| `Kernel.Path.cons_iff` | `Path step s (d :: ds) t ↔ ∃ mid, step s d mid ∧ Path step mid ds t` | derived |
| `Kernel.Path.append` | `Path step s left mid → Path step mid right t → Path step s (left ++ right) t` | derived |
| `Kernel.Path.append_iff` | `Path step s (left ++ right) t ↔ ∃ mid, Path step s left mid ∧ Path step mid right t` | derived |
| `Kernel.Path.single` | `step s d t → Path step s [d] t` | derived |
| `Kernel.Path.single_iff` | `Path step s [d] t ↔ step s d t` | derived |
| `Kernel.Path.snoc` | `Path step s ds mid → step mid d t → Path step s (ds ++ [d]) t` | derived |
| `Kernel.Path.snoc_iff` | `Path step s (ds ++ [d]) t ↔ ∃ mid, Path step s ds mid ∧ step mid d t` | derived |
| `Kernel.Path.mono` | `(∀ s d t, step s d t → step' s d t) → ∀ {s t ds}, Path step s ds t → Path step' s ds t` | derived |
| `Kernel.Path.congr` | `(∀ s d t, step s d t ↔ step' s d t) → ∀ {s t ds}, Path step s ds t ↔ Path step' s ds t` | derived |
| `Kernel.Path.map` | `(f : σ → τ) (g : L → M) → (∀ s d t, step s d t → step' (f s) (g d) (f t)) → ∀ {s t ds}, Path step s ds t → Path step' (f s) (List.map g ds) (f t)` | derived |
| `Kernel.Path.invariant` | `(∀ s d t, P s → step s d t → P t) → ∀ {s t ds}, Path step s ds t → P s → P t` | derived |
| `Kernel.Path.lift` | `(∀ s, R s s) → (∀ a b c, R a b → R b c → R a c) → (∀ s d t, step s d t → R s t) → ∀ {s t ds}, Path step s ds t → R s t` | derived |
| `Kernel.Deterministic` | `{σ : Type u_1} → {L : Type u_2} → (σ → L → σ → Prop) → Prop` | canonical |
| `Kernel.Path.deterministic` | `Deterministic step → ∀ {s t u ds}, Path step s ds t → Path step s ds u → t = u` | derived |
| `Kernel.Graph` | `{σ : Type u_1} → {L : Type u_2} → (σ → L → Option σ) → σ → L → σ → Prop` | view |
| `Kernel.run` | `{σ : Type u_1} → {L : Type u_2} → (σ → L → Option σ) → σ → List L → Option σ` | view |
| `Kernel.graph_iff` | `(next) (s t : σ) (d : L), Graph next s d t ↔ next s d = some t` | derived |
| `Kernel.graph_deterministic` | `(next), Deterministic (Graph next)` | derived |
| `Kernel.run_nil` | `(next) (s : σ), run next s [] = some s` | derived |
| `Kernel.run_cons` | `(next) (s) (d) (ds), run next s (d :: ds) = match next s d with \| some mid => run next mid ds \| none => none` | derived |
| `Kernel.path_graph_iff` | `(next) {s t : σ} {ds : List L}, Path (Graph next) s ds t ↔ run next s ds = some t` | derived |
| `Kernel.stage` | `{σ : Type u_1} → {D : Type u_2} → (σ → Option σ) → (σ → D → Option σ) → σ → Option D → Option σ` | canonical |
| `Kernel.externalWord` | `{D : Type u_1} → List (Option D) → List D` | view |
| `Kernel.Exclusive` | `{σ : Type u_1} → {D : Type u_2} → (σ → Option σ) → (σ → D → Option σ) → Prop` | canonical |
| `Kernel.prefix_comparable` | `Exclusive tick accept → ∀ (left right : List (Option D)) (s t u : σ), Path (Graph (stage tick accept)) s left t → Path (Graph (stage tick accept)) s right u → externalWord left = externalWord right → (∃ n, Path (Graph (stage tick accept)) t (List.replicate n none) u) ∨ ∃ n, Path (Graph (stage tick accept)) u (List.replicate n none) t` | derived |
| `Kernel.silent_stuck` | `(n : Nat), tick s = none → Path (Graph (stage tick accept)) s (List.replicate n none) t → t = s` | derived |
| `Kernel.normalized_unique` | `Exclusive tick accept → ∀ {s t u left right}, Path (Graph (stage tick accept)) s left t → Path (Graph (stage tick accept)) s right u → externalWord left = externalWord right → tick t = none → tick u = none → t = u` | derived |

Duplicate prevention: no constant of `Init`, of `Whatwg` or of the `effects`
package has this content. Core has `Relation.TransGen` (unlabelled, in
`Init/Core.lean`) and no labelled closure; `effects` v0.8.0 has
`Flow.Raw.ReachableFrom` over block identifiers only; lean4-effect4 at
`efcf1ae2` has `LocalSteps` over its own stores. `[C]` `Grep`.

### 3.2 Bridges (W8a, adapters)

| Module | Declaration | Signature |
| --- | --- | --- |
| `Readable.Step` | `Readable.step_eq_graph` | `∀ {α ε : Type}, Readable.Step = Kernel.Graph Readable.step` |
| `Readable.Step` | `Readable.steps_iff_path` | `∀ {α ε} {s t : Readable.State α ε} {ds : List (Readable.Decision α ε)}, Readable.Steps s ds t ↔ Kernel.Path Readable.Step s ds t` |
| `Writable.Step` | `Writable.step_iff_stage` | `∀ {α ε} (s) (d : Option (Writable.Decision α ε)) (t), Writable.Step s d t ↔ Kernel.Graph (Kernel.stage Writable.tick Writable.decide) s d t` |
| `Writable.Step` | `Writable.reaches_iff_path` | `∀ {α ε} {s t} {ds}, Writable.Reaches s ds t ↔ Kernel.Path Writable.Step s ds t` |
| `Transform.Step` | `Transform.step_iff_stage` | as Writable, over `Transform.State α β ε` |
| `Transform.Step` | `Transform.reaches_iff_path` | as Writable, over `Transform.State α β ε` |
| `Piping.Step` | `Piping.step_iff_stage` | as Writable, over `Piping.State α ε` |
| `Piping.Step` | `Piping.reaches_iff_path` | as Writable, over `Piping.State α ε` |
| `Semantics.Step` | `Ordering.step_iff_stage` | as Writable, over `Config α ε` |
| `Semantics.Step` | `Ordering.reaches_iff_path` | as Writable, over `Config α ε` |
| `Semantics.Step` | `Ordering.episodePrefix_iff_path` | `EpisodePrefix s ds t ↔ Kernel.Path (fun c d u => c.active ≠ Active.checkpoint ∧ Step c d u) s ds t` |
| `Semantics.Runs` | `Ordering.exclusive` | `∀ {α ε}, Kernel.Exclusive Ordering.tick Ordering.decide` |

Assurance route: each bridge is a receipt on the semantics edge of its
calculus graph (READABLE-PG-DEFAULT, WRITABLE-PG-DEFAULT,
TRANSFORM-PG-BACKPRESSURE, PIPING-PG-FORWARD-SHUTDOWN,
CONFIGURATION-PG-ORDERING).

### 3.3 Invariants (W8a, derived; new theorems need the breaker packet)

The signatures are those in 2.7. `Readable.QueueInv`, `Writable.QueueInv`,
`Ordering.registrationIds` and `Ordering.RegistrationsFresh` are views; the
tick, decide, step, steps or reaches, initial and reachable theorems are
derived. Assurance route: the construction edge of READABLE-PG-DEFAULT,
WRITABLE-PG-DEFAULT and CONFIGURATION-PG-ORDERING; the last discharges the
`Nodup` premise of two bridge theorems. `Ordering.CellsWellFormed` is a
statement for P8 (CFG-CELLS) and is not in W8a unless the coordinator moves
it (decision 5).
## 4. Effect on frozen surfaces

Breaker owners: P4 `readable-default`, P5 `writable-default` and its
lifecycle addendum, P6 `transform-backpressure`, P7 `piping-shutdown`, Q4
`configuration-ordering`.

| Change | P4 | P5 | P6 | P7 | Q4 | Needs a breaker amendment |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| Route B (recommended) | 0 | 0 | 0 | 0 | 0 | no change; an additive packet for the new declarations |
| Route A, with aliases | 0 | 0 | 0 | 0 | 0 | yes: the kind of 5 relations and 10 constructors changes |
| Route A, without aliases | 0 | 0 | 0 | 0 | 2 | yes |
| invariants of 2.7 | 0 | 0 | 0 | 0 | 0 | additive amendments of P4, P5 and Q4 |
| `find?` cleanup | 0 | 0 | 0 | 0 | 0 | none; proof-only |
| `fun_cases` in touched proofs | 0 | 0 | 0 | 0 | 0 | none; proof-only |
| rename the four `decide` | | 18 | 17 | 8 | 8 | yes, 51 blocks |
| `sizeCalled` reorder | | 1 | | | | yes |
| typed identifiers | ≤365 across all owners | | | | | yes |
| store fields unified | 173 field-naming blocks plus the 5 `mk` ascriptions | | | | | yes |

The Route-B and invariant rows were measured by building the prototype with
every battery untouched; the rename and identifier rows are scans of the
batteries, not builds. `[C]`

## 5. Effect on the trust gate and the strict ceiling

- No gate change. `Whatwg.Streams.Kernel` is covered by the strict prefix
  `Whatwg.Streams`; the prototype builds with 0 exceptions, and its theorems
  reach no axiom but `propext`. `[C]`
- The kernel declares no syntax and runs no metaprogram; its source uses no
  refused word. `[C]` gate pass.
- The module-closure check refuses a kernel module the audit root does not
  reach: with `Whatwg/Streams/Kernel.lean` present and imported by nothing,
  `lake build` fails with "is not reachable from the WhatwgTest audit root"
  `[C]`. W8a.1 therefore adds the import to `Whatwg/Streams.lean`.
- `lake env leanchecker Whatwg WhatwgTest WhatwgGates` over the Route B
  prototype with the in-place `fun_cases` proof: exit 0 in 80.8 s. `[C]`
- `fun_cases` is accepted in production under the strict prefix, and its
  generated principles reach `propext` only. `[C]`
- `register_simp_attr` is refused (2.8); W8 does not ask for an addendum.
- The invariant prototypes are choice-free as written. A builder who closes
  `n == n` on `Nat` with plain `simp` reaches `Classical.choice`
  (`initialCells` above); the ceiling catches it at build time.

## 6. Slices

### 6.1 Breaker packet (W8a)

Contract `test/contracts/transition-kernel.contract.md` (new), fixing the
role of `Kernel.Path`, the declarations of 3.1 and 3.2, and the reuse mode
of each per-calculus lemma (generalize). Battery
`WhatwgTest/Streams/Kernel/PathContract.lean` (ascriptions of 3.1 and 3.2)
and `WhatwgTest/Streams/Kernel/PathAxiomReport.lean`, red until the builder
lands, declared in `test/fixtures/trust-gate/known-red.txt`. Additive
amendments: `readable-default.contract.md` for `Readable.QueueInv` and its
three theorems, `writable-default.contract.md` for `Writable.QueueInv` and
its five, `configuration-ordering.contract.md` for `RegistrationsFresh` and
its four.

Counterexample seeds for `test/counterexamples/REGISTER.md`:

1. a nondeterministic one-step relation with two derivations of one label
   list to distinct ends (why `Path.deterministic` takes `Deterministic`);
2. `Writable.not_exclusive` (2.10): the comparability law fails without
   exclusivity;
3. two derivations with one external word ending at distinct states that are
   not normalized (why `normalized_unique` needs `tick t = none`);
4. the open-label `rfl` failure of `Step = Graph (stage tick decide)`, which
   is why the bridge is an iff by cases;
5. a mutant `finishEnqueue` that appends without `enqueueValueWithSize`,
   against `step_queueInv`;
6. a mutant `register` that reuses `nextObserver - 1`, against
   `step_registrationsFresh`.

### 6.2 Builder slices

| Slice | File fence | Content | Order |
| --- | --- | --- | --- |
| W8a.1 | `Whatwg/Streams/Kernel.lean` (new), `Whatwg/Streams.lean` | the kernel, appendix A | first |
| W8a.2 | the five `Step.lean`, `Writable/Laws.lean`, `Transform/Laws.lean`, `Piping/Laws.lean`, `Semantics/Runs.lean` | bridges; per-calculus lemmas and the Decision-8 laws as corollaries; delete `strip` and its helpers | after W8a.1 |
| W8a.3 | new `Readable/Invariants.lean`, `Writable/Invariants.lean` and `Semantics/Invariants.lean` (or the matching `Laws`/`Runs` files) | the three proved invariants of 2.7 | after W8a.2 |
| W8a.4 | `Whatwg/Ecma262/Promise.lean`, `Writable/Laws.lean`, `Readable/Laws.lean`, `Piping/Laws.lean` | `find?` over `map`: one keyed-update lemma, nine proof bodies | independent |
| W8a.5 | `Semantics/Configuration.lean` | the `notifySettled` docstring sentence on the owner clause | independent |
| W8b | to be fenced after W9 | the agent view and store bridges | after W9 lands |

### 6.3 What the reviewer checks

- `git diff --stat 97a8715` (or the slice base) shows no file under
  `WhatwgTest/Streams/**` changed except new kernel battery files.
- The fingerprint against the slice base shows only `=>` authored lines, all
  under `Whatwg.Streams.Kernel` or named in 3.2 and 3.3, and no `<=`
  authored line; generated-line changes are limited to the deleted private
  helpers of `Semantics/Runs.lean` and `_simp` auxiliaries.
- The gate line reports 0 strict-ceiling exceptions; `leanchecker` over the
  three prefixes passes.
- `Whatwg/Streams/Piping/Runs.lean` elaborates within its R-V5 limit.
- Each corollary re-proof derives from a kernel law, not a fresh induction.
- Model intent: every bridge is an iff, not an implication; the kernel's
  `Exclusive` is the same condition as `tick_decide_exclusive`.

### 6.4 Dependencies

- W6 (freeze registry): if W6 lands first, the W8a packet freezes through
  it; otherwise W8a freezes by `#check` ascription as today and W6 absorbs
  it. No blocking order.
- W7 (graph ledger): the kernel's receipts become ledger rows on the five
  graphs; no blocking order.
- W9 (agent record): W8b needs the five items of 2.6. If W9's agent wants
  `Kernel.Path`, decision 2 must be ruled before the W8a breaker freezes the
  module name.
- W10 (plan level): none.

## 7. Decisions for the coordinator

1. **Route.** (a) Route B; (b) Route A with aliases; (c) no kernel.
   Recommend (a). Cost: (a) a 334-line kernel, −50 net lines elsewhere, 13
   bridges, no frozen change; (b) the same kernel, a ruling naming the kind
   change of 5 relations and 10 constructors and the loss of 45 generated
   companions; (c) the 65-line `strip` and the per-calculus lemmas stay
   duplicated and no calculus gains snoc, determinism or invariant transport.
2. **Kernel location.** (a) `Whatwg.Streams.Kernel`, Streams only; (b) a
   module importable by `Whatwg.Ecma262` (a new library such as
   `WhatwgKernel`, or a module under `Whatwg.Infra` placed on the strict
   list), so W9's agent can use it. Recommend (a) unless W9's design asks for
   a relational face; (b) costs a `lakefile.toml` library, an architecture
   row, a strict-prefix addition and a DB-11 amendment.
3. **Assurance route of the kernel.** (a) local receipts linked to the laws
   edge of the five calculus graphs; (b) its own graph. Recommend (a): the
   kernel models no specification text and its laws are the composition
   receipts those graphs already hold. Cost of (b): a sixth graph document
   with ten edges for 31 generic declarations.
4. **Scope of new laws frozen in W8a.** (a) bridges and corollary re-proofs
   only; (b) plus the generic laws of 3.1; (c) plus per-calculus exclusivity
   and comparability. Recommend (b). (c) is false for Writable as measured,
   and for Transform and Piping it is a scheduler question for P8.
5. **Invariants.** (a) W8a takes the three proved in prototype (the queue
   invariant of Readable and of Writable, registration freshness);
   `CellsWellFormed` stays with P8 (CFG-CELLS), and the `notifySettled`
   docstring and D38 say the owner clause is discharged by representation;
   (b) W8a takes `CellsWellFormed` too; (c) all stay with P8. Recommend (a).
   Cost of (b): one unproved preservation theorem through every Writable
   table operation and the configuration's lift; of (c): the two `Nodup`
   premises stay undischarged.
6. **`find?` over `map`.** (a) proof-only cleanup in W8a.4; (b) leave.
   Recommend (a); it touches `Whatwg/Ecma262/Promise.lean`, owned by
   PROMISE-PG-FIRST, so that graph's owner is told.
7. **Simp sets.** (a) drop `register_simp_attr`; (b) a breaker addendum
   admitting a listed metaprogramming module and synthesised initializer
   opaques. Recommend (a); (b) contradicts R-W1(d) and lane V's opaque rule.
8. **`fun_cases`.** (a) use it in every proof W8 touches; (b) a sweep of
   every `split` cascade; (c) not at all. Recommend (a); (b) is a separate
   proof-only lane with R-V5's timing limits.
9. **The four `decide` names.** (a) keep; (b) `protected`; (c) rename.
   Recommend (a). (b) changes no fingerprint line but about 137 short uses
   in production; (c) breaks 51 frozen blocks.
10. **Typed identifiers and the `sizeCalled` order.** (a) drop; (b) defer to
    a rename lane. Recommend (a): 1 frozen equation changes meaning for the
    reorder, up to 365 blocks for typed identifiers, and no proof gains.
11. **Stores.** (a) W8b after W9 as a view with bridges; (b) unify the
    fields. Recommend (a); (b) changes 173 frozen blocks and five `mk`
    ascriptions.
12. **Schedulers and Readable's own pull reactions.** (a) P8; (b) W8.
    Recommend (a): the kernel supplies the closure, the policy is P8's.

## 8. Not checked

- Preservation of `CellsWellFormed` (statement elaborated; initialisation
  proved only through a choice-reaching `simp`).
- The `handled_bridge` and the four `Ecma262/Promise.lean` `find?` sites
  rewritten; one site was.
- `protected` on the four `decide` functions built; only counted.
- Whether W9's agent wants a relational face (decision 2).
- `leanchecker` over the Route A variants and over the invariant prototypes,
  which were elaborated as scratch files outside the tree, not inside it.
- lean4-effect4 at `efcf1ae2` was searched for a labelled closure only.
## Appendix A: the prototype kernel module

The module as it built in the prototype (`Whatwg/Streams/Kernel.lean`,
uncommitted, 334 lines), verbatim.

```lean
/-!
# Generic labelled derivations

Owner: the finite labelled derivations every Streams calculus composes from
its one-step relation, and the laws that hold of every such relation. No
calculus is defined here; each one keeps its own `Step` and its own
derivation inductive and states one bridge theorem onto `Kernel.Path`.

Spec anchors: none. This module models no algorithm of the specification;
it is proof infrastructure under the relational face of `docs/ARCHITECTURE.md`.

Fuel is not a parameter of anything here: `run` is the graph's function
form, total because a list is finite, not a fixed-fuel runner.
-/

namespace Whatwg.Streams.Kernel

universe u v w x

section Path

variable {σ : Type u} {L : Type v}

/-- Finite labelled derivations of a one-step relation. -/
inductive Path (step : σ → L → σ → Prop) : σ → List L → σ → Prop
  | nil (s : σ) : Path step s [] s
  | cons {s mid t : σ} {d : L} {ds : List L} :
      step s d mid → Path step mid ds t → Path step s (d :: ds) t

variable {step : σ → L → σ → Prop}

theorem Path.nil_iff {s t : σ} : Path step s [] t ↔ s = t := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; exact .nil s

theorem Path.cons_iff {s t : σ} {d : L} {ds : List L} :
    Path step s (d :: ds) t ↔ ∃ mid, step s d mid ∧ Path step mid ds t := by
  constructor
  · intro h; cases h with | cons first rest => exact ⟨_, first, rest⟩
  · intro ⟨_, first, rest⟩; exact .cons first rest

theorem Path.append {s mid t : σ} {left right : List L} :
    Path step s left mid → Path step mid right t → Path step s (left ++ right) t := by
  intro hl hr
  induction hl with
  | nil => exact hr
  | cons first _ ih => exact .cons first (ih hr)

theorem Path.append_iff {s t : σ} {left right : List L} :
    Path step s (left ++ right) t ↔ ∃ mid, Path step s left mid ∧ Path step mid right t := by
  constructor
  · intro h
    induction left generalizing s with
    | nil => exact ⟨s, .nil s, h⟩
    | cons d ds ih =>
        cases h with
        | cons first rest =>
            have ⟨mid, before, after⟩ := ih rest
            exact ⟨mid, .cons first before, after⟩
  · intro ⟨_, before, after⟩
    exact before.append after

theorem Path.single {s t : σ} {d : L} : step s d t → Path step s [d] t :=
  fun h => .cons h (.nil t)

theorem Path.single_iff {s t : σ} {d : L} : Path step s [d] t ↔ step s d t := by
  constructor
  · intro h
    cases h with
    | cons first rest => cases rest; exact first
  · exact Path.single

theorem Path.snoc {s mid t : σ} {ds : List L} {d : L} :
    Path step s ds mid → step mid d t → Path step s (ds ++ [d]) t :=
  fun h last => h.append (.single last)

theorem Path.snoc_iff {s t : σ} {ds : List L} {d : L} :
    Path step s (ds ++ [d]) t ↔ ∃ mid, Path step s ds mid ∧ step mid d t := by
  constructor
  · intro h
    have ⟨mid, before, after⟩ := Path.append_iff.mp h
    exact ⟨mid, before, Path.single_iff.mp after⟩
  · intro ⟨_, before, last⟩
    exact before.snoc last

/-- A derivation of a smaller relation is one of a larger relation. -/
theorem Path.mono {step' : σ → L → σ → Prop}
    (sub : ∀ s d t, step s d t → step' s d t) {s t : σ} {ds : List L} :
    Path step s ds t → Path step' s ds t := by
  intro h
  induction h with
  | nil s => exact .nil s
  | cons first _ ih => exact .cons (sub _ _ _ first) ih

/-- One-step relations that agree pointwise have the same derivations. -/
theorem Path.congr {step' : σ → L → σ → Prop}
    (same : ∀ s d t, step s d t ↔ step' s d t) {s t : σ} {ds : List L} :
    Path step s ds t ↔ Path step' s ds t :=
  ⟨Path.mono (fun s d t => (same s d t).mp), Path.mono (fun s d t => (same s d t).mpr)⟩

/-- A simulation carries derivations along a state map and a label map. -/
theorem Path.map {τ : Type w} {M : Type x} {step' : τ → M → τ → Prop}
    (f : σ → τ) (g : L → M) (sim : ∀ s d t, step s d t → step' (f s) (g d) (f t))
    {s t : σ} {ds : List L} :
    Path step s ds t → Path step' (f s) (ds.map g) (f t) := by
  intro h
  induction h with
  | nil s => exact .nil (f s)
  | cons first _ ih => exact .cons (sim _ _ _ first) ih

/-- A property every step keeps holds at the end of every derivation. -/
theorem Path.invariant {P : σ → Prop} (pres : ∀ s d t, P s → step s d t → P t)
    {s t : σ} {ds : List L} : Path step s ds t → P s → P t := by
  intro h
  induction h with
  | nil s => exact id
  | cons first _ ih => exact fun hs => ih (pres _ _ _ hs first)

/-- A reflexive, transitive relation that holds across every step holds across
every derivation. -/
theorem Path.lift {R : σ → σ → Prop} (refl : ∀ s, R s s)
    (trans : ∀ a b c, R a b → R b c → R a c) (one : ∀ s d t, step s d t → R s t)
    {s t : σ} {ds : List L} : Path step s ds t → R s t := by
  intro h
  induction h with
  | nil s => exact refl s
  | cons first _ ih => exact trans _ _ _ (one _ _ _ first) ih

/-- A one-step relation with at most one successor per state and label. -/
def Deterministic (step : σ → L → σ → Prop) : Prop :=
  ∀ s d t u, step s d t → step s d u → t = u

theorem Path.deterministic (det : Deterministic step) {s t u : σ} {ds : List L} :
    Path step s ds t → Path step s ds u → t = u := by
  intro ht
  induction ht with
  | nil s => intro hu; exact Path.nil_iff.mp hu
  | cons first _ ih =>
      intro hu
      cases hu with
      | cons first' rest' =>
          have := det _ _ _ _ first first'
          subst this
          exact ih rest'

end Path

section Graph

variable {σ : Type u} {L : Type v}

/-- The graph of a partial one-step function. -/
def Graph (next : σ → L → Option σ) (s : σ) (d : L) (t : σ) : Prop :=
  next s d = some t

/-- Run a finite label list through a partial one-step function. Total because
the list is finite; no fuel. -/
def run (next : σ → L → Option σ) : σ → List L → Option σ
  | s, [] => some s
  | s, d :: ds =>
      match next s d with
      | some mid => run next mid ds
      | none => none

theorem graph_iff (next : σ → L → Option σ) (s t : σ) (d : L) :
    Graph next s d t ↔ next s d = some t := Iff.rfl

theorem graph_deterministic (next : σ → L → Option σ) : Deterministic (Graph next) := by
  intro s d t u ht hu
  exact Option.some.inj (ht.symm.trans hu)

theorem run_nil (next : σ → L → Option σ) (s : σ) : run next s [] = some s := rfl

theorem run_cons (next : σ → L → Option σ) (s : σ) (d : L) (ds : List L) :
    run next s (d :: ds) =
      (match next s d with
       | some mid => run next mid ds
       | none => none) := rfl

/-- The relational face and the function face of a partial step agree. -/
theorem path_graph_iff (next : σ → L → Option σ) {s t : σ} {ds : List L} :
    Path (Graph next) s ds t ↔ run next s ds = some t := by
  induction ds generalizing s with
  | nil =>
      rw [Path.nil_iff, run_nil]
      exact ⟨fun h => h ▸ rfl, fun h => Option.some.inj h⟩
  | cons d ds ih =>
      rw [Path.cons_iff, run_cons]
      cases hnext : next s d with
      | none =>
          constructor
          · intro ⟨mid, first, _⟩
            have : next s d = some mid := first
            rw [hnext] at this
            exact nomatch this
          · intro h; exact nomatch h
      | some mid =>
          constructor
          · intro ⟨mid', first, rest⟩
            have : next s d = some mid' := first
            rw [hnext] at this
            cases Option.some.inj this
            exact ih.mp rest
          · intro h; exact ⟨mid, hnext, ih.mpr h⟩

end Graph

section TwoStage

variable {σ : Type u} {D : Type v}

/-- The two-stage step four calculi spell by hand: `none` is the deterministic
stage, `some d` the admission of decision `d`. -/
def stage (tick : σ → Option σ) (accept : σ → D → Option σ) : σ → Option D → Option σ
  | s, none => tick s
  | s, some d => accept s d

/-- The admitted decisions of a tape, in order, with the silent steps dropped. -/
def externalWord (labels : List (Option D)) : List D :=
  labels.filterMap id

/-- Where the deterministic stage steps, no decision is admitted. -/
def Exclusive (tick : σ → Option σ) (accept : σ → D → Option σ) : Prop :=
  ∀ s t d, tick s = some t → accept s d = none

variable {tick : σ → Option σ} {accept : σ → D → Option σ}

private theorem externalWord_none (rest : List (Option D)) :
    externalWord (none :: rest) = externalWord rest := rfl

private theorem externalWord_some (d : D) (rest : List (Option D)) :
    externalWord (some d :: rest) = d :: externalWord rest := rfl

private theorem externalWord_nil_replicate :
    ∀ (l : List (Option D)), externalWord l = [] → l = List.replicate l.length none
  | [], _ => rfl
  | none :: rest, h => by
      have hrest : externalWord rest = [] := h
      rw [List.length_cons, List.replicate_succ, ← externalWord_nil_replicate rest hrest]
  | some _ :: rest, h => by rw [externalWord_some] at h; exact nomatch h

/-- Under exclusivity, two derivations from one state that consume the same
external word differ by silent steps only. -/
theorem prefix_comparable (excl : Exclusive tick accept) :
    ∀ (left right : List (Option D)) (s t u : σ),
      Path (Graph (stage tick accept)) s left t →
      Path (Graph (stage tick accept)) s right u →
      externalWord left = externalWord right →
      (∃ n, Path (Graph (stage tick accept)) t (List.replicate n none) u) ∨
        (∃ n, Path (Graph (stage tick accept)) u (List.replicate n none) t) := by
  intro left
  induction left with
  | nil =>
      intro right s t u hl hr hw
      cases Path.nil_iff.mp hl
      have hrep := externalWord_nil_replicate right hw.symm
      exact Or.inl ⟨right.length, hrep ▸ hr⟩
  | cons d left' ih =>
      intro right s t u hl hr hw
      have ⟨mid, hstep, hrest⟩ := Path.cons_iff.mp hl
      cases d with
      | none =>
          have htick : tick s = some mid := hstep
          cases right with
          | nil =>
              cases Path.nil_iff.mp hr
              have hrep := externalWord_nil_replicate (none :: left') hw
              exact Or.inr ⟨(none :: left').length, hrep ▸ hl⟩
          | cons e right' =>
              have ⟨mid', hstep', hrest'⟩ := Path.cons_iff.mp hr
              cases e with
              | none =>
                  have hmid : mid' = mid :=
                    graph_deterministic (stage tick accept) _ _ _ _ hstep' hstep
                  subst hmid
                  exact ih right' _ t u hrest hrest'
                    (by rw [externalWord_none, externalWord_none] at hw; exact hw)
              | some e =>
                  have hnone := excl s mid e htick
                  have hcontra : accept s e = some mid' := hstep'
                  rw [hnone] at hcontra
                  exact nomatch hcontra
      | some d =>
          have hdec : accept s d = some mid := hstep
          cases right with
          | nil => rw [externalWord_some] at hw; exact nomatch hw
          | cons e right' =>
              have ⟨mid', hstep', hrest'⟩ := Path.cons_iff.mp hr
              cases e with
              | none =>
                  have htick : tick s = some mid' := hstep'
                  have hnone := excl s mid' d htick
                  rw [hnone] at hdec
                  exact nomatch hdec
              | some e =>
                  rw [externalWord_some, externalWord_some] at hw
                  have ⟨hde, hw'⟩ := List.cons.inj hw
                  subst hde
                  have hmid : mid' = mid :=
                    graph_deterministic (stage tick accept) _ _ _ _ hstep' hstep
                  subst hmid
                  exact ih right' _ t u hrest hrest' hw'

/-- A silent derivation from a state where the deterministic stage is stuck
stays put. -/
theorem silent_stuck {s t : σ} (n : Nat) (stuck : tick s = none) :
    Path (Graph (stage tick accept)) s (List.replicate n none) t → t = s := by
  intro h
  cases n with
  | zero => exact (Path.nil_iff.mp h).symm
  | succ m =>
      rw [List.replicate_succ] at h
      have ⟨mid, hstep, _⟩ := Path.cons_iff.mp h
      have hcontra : tick s = some mid := hstep
      rw [stuck] at hcontra
      exact nomatch hcontra

/-- Under exclusivity, two derivations that consume the same external word and
end where the deterministic stage is stuck end in the same state. -/
theorem normalized_unique (excl : Exclusive tick accept) {s t u : σ}
    {left right : List (Option D)} :
    Path (Graph (stage tick accept)) s left t →
    Path (Graph (stage tick accept)) s right u →
    externalWord left = externalWord right →
    tick t = none → tick u = none → t = u := by
  intro hl hr hw ht hu
  rcases prefix_comparable excl left right s t u hl hr hw with ⟨n, h⟩ | ⟨n, h⟩
  · exact (silent_stuck n ht h).symm
  · exact silent_stuck n hu h

end TwoStage

end Whatwg.Streams.Kernel
```
