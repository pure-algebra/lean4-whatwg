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

/-- A first-order promise-outcome view, distinct from an ECMAScript promise object. -/
inductive PromiseState (α ε : Type) where
  | pending
  | fulfilled (value : α)
  | rejected (reason : Boundary.Exception ε)
  deriving DecidableEq, Repr

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

/-- Eventual settlement of the promise returned by a pull callback. -/
inductive PullAnswer (ε : Type) where
  | fulfilled
  | rejected (reason : Boundary.Exception ε)
  deriving DecidableEq, Repr

/-- Synchronous pull return, before its reaction can execute. -/
inductive PullReturn (ε : Type) where
  | pending
  | settled (answer : PullAnswer ε)
  deriving DecidableEq, Repr

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
