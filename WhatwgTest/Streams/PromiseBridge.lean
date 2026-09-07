import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Breaker-owned Q3 bridging and preservation battery.
Contract: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, opened in `docs/PROMISE-DAG.md`.

This module has two halves and they fail differently.

**The preservation half is green today and must stay green.** Every `#check`
in it names an existing `Whatwg.Streams` declaration at the type P4-P7 froze,
and every `example` in it re-derives, by `rfl`, a definitional equality that
some frozen Streams receipt depends on. If any of them stops elaborating after
the builder's move-and-generalize landing, the landing is refused: R-P12's
whole argument is that an `abbrev` is a `@[reducible] def` and therefore
interchangeable at `rfl`.

**The bridging half is red today.** It names the new Streams-side views and
bridging lemmas the `generalize` rows owe. Those are additive: no existing
Streams definition body, theorem statement or `attribute [local simp]` set may
change to make them elaborate.

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ## Preservation, part 1: the three moved carriers keep their old types

`E-01`, `E-02`, `E-03` (move). After the move these are `abbrev`s; before it
they are `inductive`s. Both spellings satisfy the ascriptions below, which is
exactly the point. -/

#check (@Whatwg.Streams.Readable.PromiseState :
  Type → Type → Type)

#check (@Whatwg.Streams.Readable.PromiseState.pending :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.PromiseState α ε)

#check (@Whatwg.Streams.Readable.PromiseState.fulfilled :
  ∀ {α ε : Type}, α → Whatwg.Streams.Readable.PromiseState α ε)

#check (@Whatwg.Streams.Readable.PromiseState.rejected :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε →
    Whatwg.Streams.Readable.PromiseState α ε)

#check (@Whatwg.Streams.Readable.PullAnswer :
  Type → Type)

#check (@Whatwg.Streams.Readable.PullAnswer.fulfilled :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PullAnswer ε)

#check (@Whatwg.Streams.Readable.PullAnswer.rejected :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Readable.PullAnswer ε)

#check (@Whatwg.Streams.Readable.PullReturn :
  Type → Type)

#check (@Whatwg.Streams.Readable.PullReturn.pending :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PullReturn ε)

#check (@Whatwg.Streams.Readable.PullReturn.settled :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PullAnswer ε → Whatwg.Streams.Readable.PullReturn ε)

/-! `E-01` condition 1: the derived instances must still be found *through* the
reducible abbrev, or `decide` and the `simp` normal forms in
`Whatwg/Streams/Writable/Laws.lean` change. These four are the actual test. -/

#check (inferInstance :
  DecidableEq (Whatwg.Streams.Readable.PromiseState Unit Nat))

#check (inferInstance :
  Repr (Whatwg.Streams.Readable.PromiseState Unit Nat))

#check (inferInstance :
  DecidableEq (Whatwg.Streams.Readable.PullAnswer Nat))

#check (inferInstance :
  DecidableEq (Whatwg.Streams.Readable.PullReturn Nat))

#check (inferInstance :
  DecidableEq (Whatwg.Streams.Writable.UnitPromise Nat))

#check (inferInstance :
  DecidableEq (Whatwg.Streams.Writable.SinkJob Nat Nat))

/-! ## Preservation, part 2: the abbrevs and identity views of `E-04`..`E-12`

`E-04`, `E-05`, `E-06` (move) are re-pointed transitively: the three `Writable`
abbrevs are unchanged text over the three `Readable` names. `E-07`..`E-12`
(keep) are the identity views the plan's Q4 section already counts as the
DB-11 conversion receipts, and they must still be `rfl`. -/

#check (@Whatwg.Streams.Writable.UnitPromise :
  Type → Type)

#check (@Whatwg.Streams.Writable.SinkAnswer :
  Type → Type)

#check (@Whatwg.Streams.Writable.SinkReturn :
  Type → Type)

#check (@Whatwg.Streams.Writable.unitPromise_eq :
  ∀ {ε : Type}, Whatwg.Streams.Writable.UnitPromise ε =
    Whatwg.Streams.Readable.PromiseState Unit ε)

#check (@Whatwg.Streams.Writable.sinkAnswer_eq :
  ∀ {ε : Type}, Whatwg.Streams.Writable.SinkAnswer ε = Whatwg.Streams.Readable.PullAnswer ε)

#check (@Whatwg.Streams.Writable.sinkReturn_eq :
  ∀ {ε : Type}, Whatwg.Streams.Writable.SinkReturn ε = Whatwg.Streams.Readable.PullReturn ε)

#check (@Whatwg.Streams.Writable.unitPromise_roundtrip :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.UnitPromise ε),
    Whatwg.Streams.Writable.unitPromiseFromShared
      (Whatwg.Streams.Writable.unitPromiseToShared a) = a)

#check (@Whatwg.Streams.Writable.sinkReturnToShared_eq :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.SinkReturn ε),
    Whatwg.Streams.Writable.sinkReturnToShared a = a)

#check (@Whatwg.Streams.Writable.sinkReturn_roundtrip :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.SinkReturn ε),
    Whatwg.Streams.Writable.sinkReturnFromShared
      (Whatwg.Streams.Writable.sinkReturnToShared a) = a)

/-! These six `example`s are the definitional-equality receipts themselves,
re-derived here rather than quoted. Each must close by `rfl` before and after
the move. -/

example : ∀ {ε : Type}, Whatwg.Streams.Writable.UnitPromise ε =
    Whatwg.Streams.Readable.PromiseState Unit ε := by
  intros
  rfl

example : ∀ {ε : Type}, Whatwg.Streams.Writable.SinkAnswer ε =
    Whatwg.Streams.Readable.PullAnswer ε := by
  intros
  rfl

example : ∀ {ε : Type}, Whatwg.Streams.Writable.SinkReturn ε =
    Whatwg.Streams.Readable.PullReturn ε := by
  intros
  rfl

example : ∀ {ε : Type} (a : Whatwg.Streams.Writable.UnitPromise ε),
    Whatwg.Streams.Writable.unitPromiseFromShared
      (Whatwg.Streams.Writable.unitPromiseToShared a) = a := by
  intros
  rfl

example : ∀ {ε : Type} (a : Whatwg.Streams.Writable.SinkAnswer ε),
    Whatwg.Streams.Writable.sinkAnswerFromShared
      (Whatwg.Streams.Writable.sinkAnswerToShared a) = a := by
  intros
  rfl

example : ∀ {ε : Type} (a : Whatwg.Streams.Writable.SinkReturn ε),
    Whatwg.Streams.Writable.sinkReturnFromShared
      (Whatwg.Streams.Writable.sinkReturnToShared a) = a := by
  intros
  rfl

/-! ## Preservation, part 3: the `attribute [local simp]` functions keep their
equation lemmas

Decision 5 and inventory condition 3. Every promise-layer function named in one
of the four `attribute [local simp]` sets is `generalize`, never `move`: it
stays a `def` in `Whatwg.Streams` with its body unchanged, so `simp [f]` in
`Readable/Reentrancy.lean`, `Writable/Lifecycle.lean`, `Transform/Runs.lean`
and `Piping/Runs.lean` keeps rewriting with `f`'s own equation lemmas. The
`#check`s below pin the signatures; the `example`s below re-derive, by `rfl`,
the equation each frozen `_eq` receipt states. -/

#check (@Whatwg.Streams.Writable.lookupPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat →
    Option (Whatwg.Streams.Writable.UnitPromise ε))

#check (@Whatwg.Streams.Writable.freshPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε →
    Whatwg.Streams.Writable.UnitPromise ε → Whatwg.Streams.Writable.State α ε × Nat)

#check (@Whatwg.Streams.Writable.settle :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat →
    Except (Whatwg.Streams.Boundary.Exception ε) Unit → Whatwg.Streams.Writable.State α ε)

#check (@Whatwg.Streams.Writable.markHandled :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat →
    Whatwg.Streams.Writable.State α ε)

#check (@Whatwg.Streams.Writable.attachSink :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε →
    Whatwg.Streams.Writable.SinkOperation α ε → Whatwg.Streams.Writable.SinkReturn ε →
    Whatwg.Streams.Writable.State α ε)

#check (@Whatwg.Streams.Writable.acceptAnswer :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.SinkKind →
    Nat → Whatwg.Streams.Writable.SinkAnswer ε → Option (Whatwg.Streams.Writable.State α ε))

#check (@Whatwg.Streams.Writable.tick :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε →
    Option (Whatwg.Streams.Writable.State α ε))

#check (@Whatwg.Streams.Readable.runPullJob :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε →
    Option (Whatwg.Streams.Readable.State α ε))

#check (@Whatwg.Streams.Readable.acceptPullAnswer :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.PullAnswer ε →
    Option (Whatwg.Streams.Readable.State α ε))

#check (@Whatwg.Streams.Transform.lookupPromise :
  ∀ {α β ε : Type}, Whatwg.Streams.Transform.State α β ε → Nat →
    Option (Whatwg.Streams.Readable.PromiseState Unit ε))

#check (@Whatwg.Streams.Transform.subscriptionPromise :
  ∀ {α : Type}, Whatwg.Streams.Transform.Subscription α → Nat)

#check (@Whatwg.Streams.Transform.subscribe :
  ∀ {α β ε : Type}, Whatwg.Streams.Transform.State α β ε →
    Whatwg.Streams.Transform.Subscription α →
    Option (Whatwg.Streams.Transform.State α β ε))

#check (@Whatwg.Streams.Transform.notify :
  ∀ {α β ε : Type}, Whatwg.Streams.Transform.State α β ε →
    Whatwg.Streams.Transform.Subscription α → Whatwg.Streams.Readable.PullAnswer ε →
    Option (Whatwg.Streams.Transform.State α β ε))

#check (@Whatwg.Streams.Transform.settle :
  ∀ {α β ε : Type}, Whatwg.Streams.Transform.State α β ε → Nat →
    Whatwg.Streams.Readable.PullAnswer ε → Option (Whatwg.Streams.Transform.State α β ε))

#check (@Whatwg.Streams.Transform.runJob :
  ∀ {α β ε : Type}, Whatwg.Streams.Transform.State α β ε →
    Whatwg.Streams.Transform.Job α ε → Option (Whatwg.Streams.Transform.State α β ε))

#check (@Whatwg.Streams.Transform.tick :
  ∀ {α β ε : Type}, Whatwg.Streams.Transform.State α β ε →
    Option (Whatwg.Streams.Transform.State α β ε))

#check (@Whatwg.Streams.Piping.allWrittenSettled :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε →
    List (Whatwg.Streams.Piping.ReadWriteLink α) → Bool)

/-! The equation lemmas themselves. `simp [f]` uses these; an `abbrev` over a
general function would have only `f = General.f` instead, which is why
decision 5 answers `generalize` for every one of them. -/

example : ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat),
    Whatwg.Streams.Writable.lookupPromise s id =
      (s.promises.find? (fun p => p.1 == id)).map Prod.snd := by
  intros
  rfl

example : ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat),
    Whatwg.Streams.Writable.markHandled s id =
      (if id ∈ s.handled then s else { s with handled := s.handled ++ [id] }) := by
  intros
  rfl

example : ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε) (id : Nat),
    Whatwg.Streams.Transform.lookupPromise s id =
      (Whatwg.Streams.Writable.lookupPromise s.writable id).map
        Whatwg.Streams.Writable.unitPromiseToShared := by
  intros
  rfl

example : ∀ {α : Type} (id : Nat),
    Whatwg.Streams.Transform.subscriptionPromise
      (Whatwg.Streams.Transform.Subscription.readable (α := α) id) = id := by
  intros
  rfl

example : ∀ {α : Type} (id request : Nat),
    Whatwg.Streams.Transform.subscriptionPromise
      (Whatwg.Streams.Transform.Subscription.writable (α := α) id request) = id := by
  intros
  rfl

example : ∀ {α : Type} (id : Nat) (k : Whatwg.Streams.Transform.Reaction α),
    Whatwg.Streams.Transform.subscriptionPromise
      (Whatwg.Streams.Transform.Subscription.reaction id k) = id := by
  intros
  rfl

/-! ## Preservation, part 4: the two FIFO corollaries and their neighbours

`E-46`, `E-53`. These two statements are the corollaries the packet's general
FIFO law (`Whatwg.Ecma262.Jobs.Queue.dequeue_fifo`) must re-derive. They are
frozen P5a and P6a theorems: the packet does not restate them, it forbids their
change. -/

#check (@Whatwg.Streams.Writable.tick_job_fifo :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε)
    (job : Whatwg.Streams.Writable.SinkJob α ε)
    (jobs : List (Whatwg.Streams.Writable.SinkJob α ε)),
    Whatwg.Streams.Writable.tick { s with control := [], jobs := job :: jobs } =
      some { s with control := [.react job], jobs := jobs })

#check (@Whatwg.Streams.Writable.tick_no_job :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    s.control = [] → s.jobs = [] → Whatwg.Streams.Writable.tick s = none)

#check (@Whatwg.Streams.Transform.tick_job_fifo :
  ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε)
    (job : Whatwg.Streams.Transform.Job α ε) (tail : List (Whatwg.Streams.Transform.Job α ε)),
    s.control = [] → s.writable.control = [] → s.readable.frames = [] →
    s.jobs = job :: tail →
    Whatwg.Streams.Transform.tick s =
      Whatwg.Streams.Transform.runJob { s with jobs := tail } job)

#check (@Whatwg.Streams.Transform.tick_no_job :
  ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε),
    s.control = [] → s.writable.control = [] → s.readable.frames = [] → s.jobs = [] →
    Whatwg.Streams.Transform.tick s = none)

#check (@Whatwg.Streams.Readable.runPullJob_suspended :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    s.frames ≠ [] → Whatwg.Streams.Readable.runPullJob s = none)

#check (@Whatwg.Streams.Readable.runPullJob_empty :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    s.jobs = [] → Whatwg.Streams.Readable.runPullJob s = none)

/-! ## Preservation, part 5: the exception owner is untouched

`E-59` is `generalize`, not `move`: `Boundary.Exception`'s two identity-bearing
constructors and its `foreign` escape stay as `READABLE-PG-DEFAULT` froze them,
so the 69 dependent theorems in eight files are unchanged by construction. -/

#check (@Whatwg.Streams.Boundary.Exception :
  Type → Type)

#check (@Whatwg.Streams.Boundary.Exception.rangeError :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε)

#check (@Whatwg.Streams.Boundary.Exception.typeError :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε)

#check (@Whatwg.Streams.Boundary.Exception.foreign :
  ∀ {ε : Type}, ε → Whatwg.Streams.Boundary.Exception ε)

#check (@Whatwg.Streams.Boundary.Exception.rangeError_eq_iff :
  ∀ {ε : Type} (left right : Nat),
    (Whatwg.Streams.Boundary.Exception.rangeError left :
      Whatwg.Streams.Boundary.Exception ε) = .rangeError right ↔ left = right)

example : ∀ {ε : Type} (id : Nat),
    Whatwg.Streams.Boundary.Exception.ofRangeError (ε := ε) id .rangeError =
      .rangeError id := by
  intros
  rfl

/-! ## Bridging, part 1: the promise table views

`E-13`..`E-15`, `E-18`..`E-23` (generalize). The Streams slots and operations
stay exactly where they are; these views present them as the general table, and
the lemmas below relate each operation to its general counterpart. Decision 9
puts `handled` in the cell, so `promiseTable` reads the identity list into the
per-cell flag and `handled_bridge` is the relation decision 9 promises.

`E-22` is deliberately incomplete here. `Readable.State.readPromises` has no
`lookup`/`fresh`/`settle` of its own: every update is an inline `List.map`
inside `Readable/DefaultController.lean` and `DefaultReader.lean`. Turning
those five inline updates into `Table` calls would change a Streams definition
body, which this packet's fence forbids, so only the view and its `get` law
land now and the operation-level generalization is deferred with that reason. -/

#check (@Whatwg.Streams.Writable.promiseTable :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε →
    Whatwg.Ecma262.Promise.Table Unit (Whatwg.Streams.Boundary.Exception ε))

#check (@Whatwg.Streams.Readable.readTable :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε →
    Whatwg.Ecma262.Promise.Table (Whatwg.Streams.Readable.ReadResult α)
      (Whatwg.Streams.Boundary.Exception ε))

#check (@Whatwg.Streams.Writable.promiseTable_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.promiseTable s =
      Whatwg.Ecma262.Promise.Table.mk
        (s.promises.map (fun p =>
          (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 (decide (p.1 ∈ s.handled)))))
        s.nextPromise)

#check (@Whatwg.Streams.Writable.lookupPromise_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat),
    Whatwg.Streams.Writable.lookupPromise s id =
      Whatwg.Ecma262.Promise.Table.get (Whatwg.Streams.Writable.promiseTable s) id)

#check (@Whatwg.Streams.Writable.freshPromise_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε)
    (outcome : Whatwg.Streams.Writable.UnitPromise ε),
    s.nextPromise ∉ s.handled →
      (Whatwg.Streams.Writable.promiseTable (Whatwg.Streams.Writable.freshPromise s outcome).1,
        (Whatwg.Streams.Writable.freshPromise s outcome).2) =
        Whatwg.Ecma262.Promise.Table.fresh (Whatwg.Streams.Writable.promiseTable s) outcome)

#check (@Whatwg.Streams.Writable.settle_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat)
    (result : Except (Whatwg.Streams.Boundary.Exception ε) Unit),
    Whatwg.Streams.Writable.promiseTable (Whatwg.Streams.Writable.settle s id result) =
      Whatwg.Ecma262.Promise.Table.settle (Whatwg.Streams.Writable.promiseTable s) id result)

#check (@Whatwg.Streams.Writable.markHandled_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat),
    Whatwg.Streams.Writable.promiseTable (Whatwg.Streams.Writable.markHandled s id) =
      Whatwg.Ecma262.Promise.Table.markHandled (Whatwg.Streams.Writable.promiseTable s) id)

/-! Decision 9's bridging lemma: the per-cell flag agrees with membership of
the identity list wherever the cell exists. -/
#check (@Whatwg.Streams.Writable.handled_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat),
    (Whatwg.Ecma262.Promise.Table.getCell (Whatwg.Streams.Writable.promiseTable s) id).map
        Whatwg.Ecma262.Promise.Cell.handled =
      (Whatwg.Streams.Writable.lookupPromise s id).map (fun _ => decide (id ∈ s.handled)))

#check (@Whatwg.Streams.Readable.readTable_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.readTable s =
      Whatwg.Ecma262.Promise.Table.mk
        (s.readPromises.map (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false)))
        s.nextRead)

#check (@Whatwg.Streams.Readable.readTable_get :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (id : Nat),
    Whatwg.Ecma262.Promise.Table.get (Whatwg.Streams.Readable.readTable s) id =
      (s.readPromises.find? (fun p => p.1 == id)).map Prod.snd)

/-! ## Bridging, part 2: the three job queues

`E-45`, `E-46`, `E-48`, `E-49`, `E-52`, `E-53` (generalize). `E-46` records
that the writable queue stage is one branch of a twenty-branch `tick`, so the
honest bridging lemma is that `tick` *reduces to* `Queue.dequeue` under the
component's own spelling of "the execution context stack is empty". The three
lemmas below are that reduction; `tick_job_fifo`, `tick_no_job` and the three
`runPullJob_*` receipts follow from them and the general FIFO law. -/

#check (@Whatwg.Streams.Writable.jobQueue :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Streams.Writable.SinkJob α ε))

#check (@Whatwg.Streams.Readable.jobQueue :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Streams.Readable.PullAnswer ε))

#check (@Whatwg.Streams.Transform.jobQueue :
  ∀ {α β ε : Type}, Whatwg.Streams.Transform.State α β ε →
    Whatwg.Ecma262.Jobs.Queue (Whatwg.Streams.Transform.Job α ε))

#check (@Whatwg.Streams.Writable.jobQueue_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.jobQueue s = Whatwg.Ecma262.Jobs.Queue.mk s.jobs)

#check (@Whatwg.Streams.Readable.jobQueue_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.jobQueue s = Whatwg.Ecma262.Jobs.Queue.mk s.jobs)

#check (@Whatwg.Streams.Transform.jobQueue_eq :
  ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε),
    Whatwg.Streams.Transform.jobQueue s = Whatwg.Ecma262.Jobs.Queue.mk s.jobs)

/-! `E-46`. Mask M2. -/
#check (@Whatwg.Streams.Writable.tick_dequeue_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    s.control = [] →
      Whatwg.Streams.Writable.tick s =
        (Whatwg.Ecma262.Jobs.Queue.dequeue (Whatwg.Streams.Writable.jobQueue s)).map
          (fun p => { s with control := [.react p.1], jobs := p.2.pending }))

/-! `E-49`. Mask M2. -/
#check (@Whatwg.Streams.Readable.runPullJob_dequeue_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    s.frames = [] →
      Whatwg.Streams.Readable.runPullJob s =
        (Whatwg.Ecma262.Jobs.Queue.dequeue (Whatwg.Streams.Readable.jobQueue s)).map
          (fun p => Whatwg.Streams.Readable.reactPull { s with jobs := p.2.pending } p.1))

/-! `E-53`. Mask M2. The three-part guard is the clearest statement in the
repository of `requirement.jobs.1`, and it is stated today only as a hypothesis
of `tick_job_fifo`; here it is the hypothesis of the bridge. -/
#check (@Whatwg.Streams.Transform.tick_dequeue_bridge :
  ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε),
    s.control = [] → s.writable.control = [] → s.readable.frames = [] →
      Whatwg.Streams.Transform.tick s =
        (Whatwg.Ecma262.Jobs.Queue.dequeue (Whatwg.Streams.Transform.jobQueue s)).bind
          (fun p => Whatwg.Streams.Transform.runJob { s with jobs := p.2.pending } p.1))

/-! `E-37` (generalize), the queueing half only: `attachSink` also clears the
close and abort algorithm slots, which the general `react` must not do, so the
bridge is stated on the job queue alone. Mask M2. -/
#check (@Whatwg.Streams.Writable.attachSink_settled_jobs :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε)
    (op : Whatwg.Streams.Writable.SinkOperation α ε)
    (answer : Whatwg.Streams.Writable.SinkAnswer ε),
    Whatwg.Streams.Writable.jobQueue
        (Whatwg.Streams.Writable.attachSink s op (.settled answer)) =
      Whatwg.Ecma262.Jobs.Queue.enqueue (Whatwg.Streams.Writable.jobQueue s)
        ⟨Whatwg.Streams.Writable.operationKind op,
          Whatwg.Streams.Writable.operationRequest op, answer⟩)

#check (@Whatwg.Streams.Writable.attachSink_pending_jobs :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε)
    (op : Whatwg.Streams.Writable.SinkOperation α ε),
    Whatwg.Streams.Writable.jobQueue (Whatwg.Streams.Writable.attachSink s op .pending) =
      Whatwg.Streams.Writable.jobQueue s)

/-! `E-38` (generalize), the queueing half only. Mask M2. -/
#check (@Whatwg.Streams.Writable.acceptAnswer_jobs :
  ∀ {α ε : Type} (s t : Whatwg.Streams.Writable.State α ε)
    (kind : Whatwg.Streams.Writable.SinkKind) (id : Nat)
    (answer : Whatwg.Streams.Writable.SinkAnswer ε),
    Whatwg.Streams.Writable.acceptAnswer s kind id answer = some t →
      Whatwg.Streams.Writable.jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueue (Whatwg.Streams.Writable.jobQueue s)
          ⟨kind, id, answer⟩)

/-! ## Bridging, part 3: the reaction list

`E-29`, `E-30`, `E-31` (generalize) and decision 8. `Transform.State.subscriptions`
is the one-list view of the two general lists: `reactions` builds both lists
positionally, giving the paired entries one id, and `Reactions.registered` is
the fulfil list, so the registration order Streams records is preserved. -/

#check (@Whatwg.Streams.Transform.reactions :
  ∀ {α β ε : Type}, Whatwg.Streams.Transform.State α β ε →
    Whatwg.Ecma262.Promise.Reactions (Whatwg.Streams.Transform.Subscription α))

#check (@Whatwg.Streams.Transform.reactions_next :
  ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε),
    (Whatwg.Streams.Transform.reactions s).next = s.subscriptions.length)

#check (@Whatwg.Streams.Transform.reactions_registered :
  ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε),
    (Whatwg.Ecma262.Promise.Reactions.registered
      (Whatwg.Streams.Transform.reactions s)).filterMap
        Whatwg.Ecma262.Promise.Reaction.handler = s.subscriptions)

/-! `E-30`: the identity captured at registration, independent of later slot
replacement, agrees with the general accessor. -/
#check (@Whatwg.Streams.Transform.reactions_promises :
  ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε),
    (Whatwg.Ecma262.Promise.Reactions.registered
      (Whatwg.Streams.Transform.reactions s)).map Whatwg.Ecma262.Promise.Reaction.promise =
      s.subscriptions.map Whatwg.Streams.Transform.subscriptionPromise)

/-! `E-31`: the pending branch of `subscribe` is `Reactions.add`. The two
settled branches dispatch into the canonical component (`E-32` risk) and are
therefore bridged on the job queue by the transform builder, not here. -/
#check (@Whatwg.Streams.Transform.subscribe_reactions_bridge :
  ∀ {α β ε : Type} (s : Whatwg.Streams.Transform.State α β ε)
    (sub : Whatwg.Streams.Transform.Subscription α),
    Whatwg.Streams.Transform.lookupPromise s
        (Whatwg.Streams.Transform.subscriptionPromise sub) = some .pending →
      (Whatwg.Streams.Transform.subscribe s sub).map Whatwg.Streams.Transform.reactions =
        some (Whatwg.Ecma262.Promise.Reactions.add (Whatwg.Streams.Transform.reactions s)
          (Whatwg.Streams.Transform.subscriptionPromise sub) (some sub) (some sub)).1)

/-! ## Bridging, part 4: the settled predicate

`E-55`, `E-56` (generalize) and decision 11. The two Streams forms are the
`Prop` and `Bool` faces of `Whatwg.WebIdl.Promise.AllSettled` over the writable
table, restricted to links whose write has been submitted. `G-06` records what
is still absent, and this packet's `waitForAll` supplies the ordered result and
the short-circuit but not the returned promise. -/

#check (@Whatwg.Streams.Piping.allWrittenSettled_bridge :
  ∀ {α ε : Type} (w : Whatwg.Streams.Writable.State α ε)
    (ls : List (Whatwg.Streams.Piping.ReadWriteLink α)),
    (∀ l ∈ ls, ∃ call request,
        l.write = Whatwg.Streams.Piping.WriteStage.submitted call request) →
      Whatwg.Streams.Piping.allWrittenSettled w ls =
        Whatwg.WebIdl.Promise.allSettled (Whatwg.Streams.Writable.promiseTable w)
          (ls.filterMap (fun l => match l.write with
            | .submitted _ request => some request
            | _ => none)))

#check (@Whatwg.Streams.Piping.writesSettled_bridge :
  ∀ {α ε : Type} (s : Whatwg.Streams.Piping.Snapshot α ε),
    (∀ l ∈ s.links, ∃ call request,
        l.write = Whatwg.Streams.Piping.WriteStage.submitted call request) →
      (Whatwg.Streams.Piping.WritesSettled s ↔
        Whatwg.WebIdl.Promise.AllSettled
          (Whatwg.Streams.Writable.promiseTable s.destination)
          (s.links.filterMap (fun l => match l.write with
            | .submitted _ request => some request
            | _ => none))))

/-! ## Bridging, part 5: the exception embedding (part C, R-P14)

`E-59` (generalize), `E-60`, `E-61` (keep). The embedding preserves the
allocation identity, and the retraction recovers the Streams reason exactly, so
the two kinds Streams models sit inside the five-kind Web IDL universe without
either type changing. All five laws are mask M1. -/

#check (@Whatwg.Streams.Boundary.Exception.toWebIdl :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε →
    Whatwg.WebIdl.Exceptions.Exception ε)

#check (@Whatwg.Streams.Boundary.Exception.ofWebIdl :
  ∀ {ε : Type}, Whatwg.WebIdl.Exceptions.Exception ε →
    Option (Whatwg.Streams.Boundary.Exception ε))

#check (@Whatwg.Streams.Boundary.Exception.toWebIdl_rangeError :
  ∀ {ε : Type} (id : Nat),
    Whatwg.Streams.Boundary.Exception.toWebIdl
        (Whatwg.Streams.Boundary.Exception.rangeError id :
          Whatwg.Streams.Boundary.Exception ε) =
      Whatwg.WebIdl.Exceptions.Exception.simple
        Whatwg.WebIdl.Exceptions.Simple.rangeError id)

#check (@Whatwg.Streams.Boundary.Exception.toWebIdl_typeError :
  ∀ {ε : Type} (id : Nat),
    Whatwg.Streams.Boundary.Exception.toWebIdl
        (Whatwg.Streams.Boundary.Exception.typeError id :
          Whatwg.Streams.Boundary.Exception ε) =
      Whatwg.WebIdl.Exceptions.Exception.simple
        Whatwg.WebIdl.Exceptions.Simple.typeError id)

#check (@Whatwg.Streams.Boundary.Exception.toWebIdl_foreign :
  ∀ {ε : Type} (r : ε),
    Whatwg.Streams.Boundary.Exception.toWebIdl (Whatwg.Streams.Boundary.Exception.foreign r) =
      Whatwg.WebIdl.Exceptions.Exception.foreign r)

#check (@Whatwg.Streams.Boundary.Exception.ofWebIdl_toWebIdl :
  ∀ {ε : Type} (e : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Boundary.Exception.ofWebIdl
      (Whatwg.Streams.Boundary.Exception.toWebIdl e) = some e)

/-! R-P14: a Web IDL exception without an allocation identity cannot host the
nested-size-callback distinctness witnesses, so the embedding is injective. -/
#check (@Whatwg.Streams.Boundary.Exception.toWebIdl_injective :
  ∀ {ε : Type} (left right : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Boundary.Exception.toWebIdl left =
      Whatwg.Streams.Boundary.Exception.toWebIdl right → left = right)

/-! `E-60` (keep): P3-R2's embedding, read through the Web IDL universe, is
`op.to-create-a-simple-exception` at the identity the consuming calculus
allocated. -/
#check (@Whatwg.Streams.Boundary.Exception.toWebIdl_ofRangeError :
  ∀ {ε : Type} (id : Nat) (e : Whatwg.Streams.Data.RangeError),
    Whatwg.Streams.Boundary.Exception.toWebIdl
        (Whatwg.Streams.Boundary.Exception.ofRangeError (ε := ε) id e) =
      Whatwg.WebIdl.Exceptions.createSimple
        Whatwg.WebIdl.Exceptions.Simple.rangeError id)
