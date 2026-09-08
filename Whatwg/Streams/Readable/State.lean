import Whatwg.Ecma262.Promise
import Whatwg.Streams.Boundary.Exception
import Whatwg.Streams.Data.DyadicSize
import Whatwg.Streams.Data.Strategy

/-!
# Default-readable state and observations

The declaration records and span digests are frozen in `docs/READABLE-DAG.md`.
This is the post-start, attached-default-reader view of `READABLE-PG-DEFAULT`.
It stores no callback bodies or host promises. Raw records need not be reachable;
in particular terminal states and pending reads may coexist with queued chunks.
Full-state, global allocation, and host observation embeddings remain open.
-/

namespace Whatwg.Streams.Readable

-- Core's Except has no DecidableEq instance. Keep this deriving aid private and local;
-- comparisons still reduce by inspecting the two constructors and their data.
@[instance_reducible] private def exceptDecidableEq {α ε : Type} [DecidableEq α] [DecidableEq ε] :
    DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

attribute [local instance] exceptDecidableEq

/-- P3's canonical exact carrier, under the existing binary64 rounding boundary. -/
abbrev Size := Data.DyadicSize

/-- The P3 arithmetic interface used by the default-controller slot view. -/
def sizes : Data.SizeClass Size := Data.DyadicSize.sizes

/-- The named view introduces no second numeric carrier. -/
theorem size_eq : Size = Data.DyadicSize := rfl

/-- The arithmetic view is P3's ruled instance. -/
theorem sizes_eq : sizes = Data.DyadicSize.sizes := rfl

/-- The stream state and stored-error slot as one tagged value. -/
inductive Status (ε : Type) where
  | readable
  | closed
  | errored (reason : Boundary.Exception ε)
  deriving DecidableEq, Repr

/-- The result delivered by a default read request. -/
inductive ReadResult (α : Type) where
  | chunk (value : α)
  | done
  deriving DecidableEq, Repr

/-- A first-order promise-outcome view, distinct from an ECMAScript promise object.
`E-01` (move, `PROMISE-PG-FIRST`): the carrier now lives in `Whatwg.Ecma262.Promise`
at `slot.PromiseState`/`slot.PromiseResult`, and this reducible view keeps every
dependent proof unchanged by definitional equality. -/
abbrev PromiseState (α ε : Type) :=
  Whatwg.Ecma262.Promise.State α (Boundary.Exception ε)

namespace PromiseState

/-- `E-01`: the moved `pending` constructor at its pre-move Streams type. -/
abbrev pending {α ε : Type} : PromiseState α ε :=
  Whatwg.Ecma262.Promise.State.pending

/-- `E-01`: the moved `fulfilled` constructor at its pre-move Streams type. -/
abbrev fulfilled {α ε : Type} (value : α) : PromiseState α ε :=
  Whatwg.Ecma262.Promise.State.fulfilled value

/-- `E-01`: the moved `rejected` constructor at its pre-move Streams type. -/
abbrev rejected {α ε : Type} (reason : Boundary.Exception ε) : PromiseState α ε :=
  Whatwg.Ecma262.Promise.State.rejected reason

end PromiseState

/-- Names of the installed foreign algorithms; clearing removes the entire optional record. -/
structure Algorithms where
  size : Data.SizeAlgorithm Nat
  pull : Nat
  cancel : Nat
  deriving DecidableEq, Repr

/-- Observable closed/read promise settlements, with the read's allocated identity. -/
inductive Settlement (α ε : Type) where
  | closed (result : Except (Boundary.Exception ε) Unit)
  | read (id : Nat) (result : Except (Boundary.Exception ε) (ReadResult α))
  deriving DecidableEq, Repr

/-- Internal invocations and the visible results whose order the local masks project. -/
inductive Event (α ε : Type) where
  | sizeCalled (call algorithm : Nat) (chunk : α)
  | pullCalled (algorithm : Nat)
  | enqueueReturned (call : Nat) (result : Except (Boundary.Exception ε) Unit)
  | settled (settlement : Settlement α ε)
  | desiredSizeRead (result : Option Size)
  deriving DecidableEq, Repr

/-- Work following a synchronous pull call, represented as data rather than a closure. -/
inductive PullContinuation (α : Type) where
  | done
  | settleRead (id : Nat) (chunk : α)
  | returnEnqueue (call : Nat)
  deriving DecidableEq, Repr

/-- Synchronous callback suspension markers in last-in, first-out order. -/
inductive Frame (α : Type) where
  | size (call : Nat) (chunk : α)
  | pull (continuation : PullContinuation α)
  deriving DecidableEq, Repr

/-- Eventual settlement of the promise returned by a pull callback.
`E-02` (move, `PROMISE-PG-FIRST`): the carrier now lives in
`Whatwg.Ecma262.Promise` at `op.fulfillpromise`/`op.rejectpromise`. -/
abbrev PullAnswer (ε : Type) :=
  Whatwg.Ecma262.Promise.Outcome (Boundary.Exception ε)

namespace PullAnswer

/-- `E-02`: the moved `fulfilled` constructor at its pre-move Streams type. -/
abbrev fulfilled {ε : Type} : PullAnswer ε :=
  Whatwg.Ecma262.Promise.Outcome.fulfilled

/-- `E-02`: the moved `rejected` constructor at its pre-move Streams type. -/
abbrev rejected {ε : Type} (reason : Boundary.Exception ε) : PullAnswer ε :=
  Whatwg.Ecma262.Promise.Outcome.rejected reason

end PullAnswer

/-- Synchronous pull return, before its reaction can execute.
`E-03` (move, `PROMISE-PG-FIRST`): the carrier now lives in
`Whatwg.Ecma262.Promise` as the returned-promise slot value. -/
abbrev PullReturn (ε : Type) :=
  Whatwg.Ecma262.Promise.Returned (Boundary.Exception ε)

namespace PullReturn

/-- `E-03`: the moved `pending` constructor at its pre-move Streams type. -/
abbrev pending {ε : Type} : PullReturn ε :=
  Whatwg.Ecma262.Promise.Returned.pending

/-- `E-03`: the moved `settled` constructor at its pre-move Streams type. -/
abbrev settled {ε : Type} (answer : PullAnswer ε) : PullReturn ε :=
  Whatwg.Ecma262.Promise.Returned.settled answer

end PullReturn

/-- Raw slot projection of a single stream, controller, and attached default reader. -/
structure State (α ε : Type) where
  status : Status ε
  queue : Data.Queue α Size
  highWaterMark : Size
  started : Bool
  closeRequested : Bool
  pulling : Bool
  pullAgain : Bool
  algorithms : Option Algorithms
  readRequests : List Nat
  nextRead : Nat
  nextEnqueue : Nat
  nextError : Nat
  closedPromise : PromiseState Unit ε
  readPromises : List (Nat × PromiseState (ReadResult α) ε)
  frames : List (Frame α)
  pullAwaiting : Bool
  jobs : List (PullAnswer ε)
  trace : List (Event α ε)

/-- `E-48` (generalize, `PROMISE-PG-FIRST`): the pull-answer job list read as the general
`hook.hostenqueuepromisejob` queue, at payload `PullAnswer ε`. -/
def jobQueue {α ε : Type} (s : State α ε) : Whatwg.Ecma262.Jobs.Queue (PullAnswer ε) :=
  Whatwg.Ecma262.Jobs.Queue.mk s.jobs

/-- `E-22` (generalize, `PROMISE-PG-FIRST`): the read-promise slots read as the general
promise table, at value parameter `ReadResult α`. This is why the general state needs two
type parameters (decision 1). The operation-level generalization of `E-22` landed at slice
Q4 as `freshReadCell`, `settleReadCell` and `settleReadCells` below, with
`readTable_freshReadCell`, `readTable_settleReadCell` and `readTable_settleReadCells` in
`Whatwg/Streams/Readable/Laws.lean` as their bridges onto this view. -/
def readTable {α ε : Type} (s : State α ε) :
    Whatwg.Ecma262.Promise.Table (ReadResult α) (Boundary.Exception ε) :=
  Whatwg.Ecma262.Promise.Table.mk
    (s.readPromises.map (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false)))
    s.nextRead

/-- `E-22` (generalize, Q4): allocate a read cell at the cursor. The Streams
instance of `Whatwg.Ecma262.Promise.Table.fresh` at value parameter
`ReadResult α`. -/
@[simp] def freshReadCell {α ε : Type} (s : State α ε)
    (outcome : PromiseState (ReadResult α) ε) : State α ε × Nat :=
  ({ s with
      nextRead := s.nextRead + 1,
      readPromises := s.readPromises ++ [(s.nextRead, outcome)] },
    s.nextRead)

/-- `E-22` (generalize, Q4): overwrite one read cell. Deliberately unguarded,
exactly as the inline `List.map` updates are: the general `Table.settle` is
guarded by `isPending` and a non-pending settle is the identity (decision 7),
so the two agree only under the pending hypothesis, which is where
`Table.settle_pending` puts them. Adopting the guard here would change the
meaning of four landed Streams bodies. -/
@[simp] def settleReadCell {α ε : Type} (s : State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) (ReadResult α)) : State α ε :=
  { s with
    readPromises := s.readPromises.map (fun p =>
      if p.1 = id then
        (p.1, match result with | .ok v => .fulfilled v | .error e => .rejected e)
      else p) }

/-- `E-22` (generalize, Q4): overwrite every read cell whose identity is in
`ids`. The two set-shaped updates of `streamClose` and `error` are its
instances. -/
@[simp] def settleReadCells {α ε : Type} (s : State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) (ReadResult α)) : State α ε :=
  { s with
    readPromises := s.readPromises.map (fun p =>
      if p.1 ∈ ids then
        (p.1, match result with | .ok v => .fulfilled v | .error e => .rejected e)
      else p) }

/-- The frozen post-start view, before its first demand check; not the full setup algorithm. -/
def initial {α ε : Type} (algorithms : Algorithms) (hwm : Size) : State α ε :=
  { status := .readable, queue := Data.Queue.empty sizes, highWaterMark := hwm,
    started := true, closeRequested := false, pulling := false, pullAgain := false,
    algorithms := some algorithms, readRequests := [], nextRead := 0, nextEnqueue := 0,
    nextError := 0, closedPromise := .pending, readPromises := [], frames := [],
    pullAwaiting := false, jobs := [], trace := [] }

/-- `op.readable-stream-default-controller-should-call-pull`: positivity in the exact view. -/
def sizePositive : Size → Bool
  | .posInfinity => true
  | .finite units => decide (0 < units)
  | _ => false

/-- The settlement-order component of local M2, not the whole mask. -/
def settlementTrace {α ε : Type} (s : State α ε) : List (Settlement α ε) :=
  s.trace.filterMap fun event => match event with
    | .settled value => some value
    | _ => none

/-- Successful chunk deliveries in settlement order. -/
def chunksOfSettlements {α ε : Type} (events : List (Settlement α ε)) : List α :=
  events.filterMap fun event => match event with
    | .read _ (.ok (.chunk value)) => some value
    | _ => none

/-- Local M1: delivered chunks and current status; readable denotes a live frontier. -/
def observeM1 {α ε : Type} (s : State α ε) : List α × Status ε :=
  (chunksOfSettlements (settlementTrace s), s.status)

/-- The consumer-visible component of the default-readable event alphabet. -/
inductive VisibleEvent (α ε : Type) where
  | settlement (value : Settlement α ε)
  | desiredSizeRead (result : Option Size)
  | enqueueReturned (call : Nat) (result : Except (Boundary.Exception ε) Unit)
  deriving DecidableEq, Repr

/-- Local M2 contains M1 and ordered visible events; the full-stream embedding remains open. -/
structure M2Observation (α ε : Type) where
  m1 : List α × Status ε
  visible : List (VisibleEvent α ε)
  deriving DecidableEq, Repr

/-- Local M2 includes desiredSize queries and completed enqueue calls as well as settlements. -/
def observeM2 {α ε : Type} (s : State α ε) : M2Observation α ε :=
  ⟨observeM1 s, s.trace.filterMap fun event => match event with
    | .settled value => some (.settlement value)
    | .desiredSizeRead result => some (.desiredSizeRead result)
    | .enqueueReturned call result => some (.enqueueReturned call result)
    | _ => none⟩

end Whatwg.Streams.Readable
