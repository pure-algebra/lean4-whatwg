import Whatwg.Streams.Readable.DefaultReader
import Whatwg.Streams.Writable.DefaultWriter

/-!
# Transform.Stream.lean

Owner: the `TransformStream` state as a first-order record: the readable and
writable halves it owns, the backpressure change signal, and the
stream-level abstract operations.

Spec anchors: `ts-class`, `ts-internal-slots`, `ts-abstract-ops`.

The frozen TRANSFORM-PG-BACKPRESSURE packet owns this count-output projection.
The readable and writable components retain their canonical types. Global
allocation, setup/start, lifecycle and DB-04 embeddings remain open.
-/

namespace Whatwg.Streams.Transform

/-- Native port names of `op.initialize-transform-stream`; these are owned internal calls. -/
structure Ports where
  pull : Nat
  readCancel : Nat
  write : Nat
  close : Nat
  abort : Nat
  deriving Repr, DecidableEq

/-- Foreign algorithm names; `op.transform-stream-default-controller-clear-algorithms`. -/
structure Algorithms where
  transform : Nat
  flush : Nat
  cancel : Nat
  deriving Repr, DecidableEq

/-- Result routing for `op.transform-stream-default-sink-write-algorithm`. -/
inductive Completion where
  | direct
  | adopt (resultPromise : Nat)
  deriving Repr, DecidableEq

/-- First-order reactions for the sink-write and PerformTransform algorithms. -/
inductive Reaction (α : Type) where
  | write (request : Nat) (chunk : α) (resultPromise : Nat)
  | transform (resultPromise : Nat)
  | adopt (resultPromise : Nat)
  deriving Repr

/-- Captured promise subscriptions; `op.transform-stream-set-backpressure`. -/
inductive Subscription (α : Type) where
  | readable (promise : Nat)
  | writable (promise request : Nat)
  | reaction (promise : Nat) (reaction : Reaction α)
  deriving Repr

/-- The identity captured at registration, independent of subsequent slot replacement. -/
def subscriptionPromise {α : Type} : Subscription α → Nat
  | .readable promise | .writable promise _ | .reaction promise _ => promise

/-- Ordered component-job tags and transform reactions; canonical component bodies are reused. -/
inductive Job (α ε : Type) where
  | readable (promise : Nat)
  | writable (request : Nat)
  | reaction (reaction : Reaction α) (answer : Readable.PullAnswer ε)
  deriving Repr

/-- Suspended foreign calls and deterministic error/unblock/settlement continuations. -/
inductive Control (ε : Type) where
  | awaitTransform (request : Nat) (completion : Completion) (writableDepth : Nat)
  | errorWritable (reason : Boundary.Exception ε)
  | waitWritable (depth : Nat)
  | unblock
  | settle (promise : Nat) (answer : Readable.PullAnswer ε)
  deriving Repr

/-- Joint component events and public transformer operations; not itself an observation mask. -/
inductive Event (α β ε : Type) where
  | readable (event : Readable.Event β ε)
  | writable (event : Writable.Event α ε)
  | transformCalled (request algorithm : Nat) (chunk : α)
  | transformReturned (request resultPromise : Nat)
  | enqueueReturned (call : Nat) (result : Except (Boundary.Exception ε) Unit)
  deriving Repr

/--
The frozen `op.initialize-transform-stream` projection: actual P4/P5 components
plus transform-owned slots and continuations. The shared table belongs to P5.
-/
structure State (α β ε : Type) where
  readable : Readable.State β ε
  writable : Writable.State α ε
  ports : Ports
  backpressure : Bool
  backpressurePromise : Nat
  internalPromises : List Nat
  algorithms : Option Algorithms
  subscriptions : List (Subscription α)
  jobs : List (Job α ε)
  control : List (Control ε)
  pendingTransforms : List (Nat × Nat)
  nextCall : Nat
  trace : List (Event α β ε)

/-- Lift a canonical readable transition's trace suffix; prefix validity is a later invariant. -/
def withReadable {α β ε : Type} (s : State α β ε) (r : Readable.State β ε) : State α β ε :=
  { s with
    readable := r,
    trace := s.trace ++ (r.trace.drop s.readable.trace.length).map Event.readable }

/-- Lift a canonical writable transition's trace suffix, retaining all transform-owned slots. -/
def withWritable {α β ε : Type} (s : State α β ε) (w : Writable.State α ε) : State α β ε :=
  { s with
    writable := w,
    trace := s.trace ++ (w.trace.drop s.writable.trace.length).map Event.writable }

/--
Count-profile tail of successful start, under `op.initialize-transform-stream`
and `op.set-up-readable-stream-default-controller`. Actual native pull work is
staged before an external call can be admitted.
-/
def initial {α β ε : Type} (readHwm writeHwm : Data.DyadicSize)
    (inputSize : Data.SizeAlgorithm Nat) (ports : Ports) (algorithms : Algorithms)
    (promiseSeed errorSeed : Nat) : State α β ε :=
  let r := Readable.callPullIfNeeded (Readable.initial
    { size := .one, pull := ports.pull, cancel := ports.readCancel } readHwm)
  let w := Writable.initial writeHwm
    { size := some inputSize, write := some (.foreign ports.write),
      close := some (.foreign ports.close), abort := some (.foreign ports.abort) }
    promiseSeed errorSeed
  let (w', bp) := Writable.freshPromise w .pending
  { readable := r, writable := w', ports := ports, backpressure := true,
    backpressurePromise := bp, internalPromises := [bp], algorithms := some algorithms,
    subscriptions := [], jobs := [], control := [], pendingTransforms := [],
    nextCall := 0, trace := r.trace.map Event.readable }

end Whatwg.Streams.Transform
