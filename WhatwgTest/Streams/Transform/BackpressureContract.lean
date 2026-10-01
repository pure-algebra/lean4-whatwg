import Whatwg.Streams
import WhatwgTest.Audit.Freeze

/-! Frozen P6a exact surface, 2026-09-05.
Graph: TRANSFORM-PG-BACKPRESSURE. Count output profile; canonical P4/P5 coupling.
The symbols below are planned production declarations, never local replacement runtimes.
-/

set_option autoImplicit false
open Whatwg.Streams

#whatwg_freeze (@Transform.Ports :
  Type)

#whatwg_freeze (@Transform.Ports.mk :
  Nat → Nat → Nat → Nat → Nat → Transform.Ports)

#whatwg_freeze (@Transform.Ports.pull :
  Transform.Ports → Nat)

#whatwg_freeze (@Transform.Ports.readCancel :
  Transform.Ports → Nat)

#whatwg_freeze (@Transform.Ports.write :
  Transform.Ports → Nat)

#whatwg_freeze (@Transform.Ports.close :
  Transform.Ports → Nat)

#whatwg_freeze (@Transform.Ports.abort :
  Transform.Ports → Nat)

#whatwg_freeze (@Transform.Algorithms :
  Type)

#whatwg_freeze (@Transform.Algorithms.mk :
  Nat → Nat → Nat → Transform.Algorithms)

#whatwg_freeze (@Transform.Algorithms.transform :
  Transform.Algorithms → Nat)

#whatwg_freeze (@Transform.Algorithms.flush :
  Transform.Algorithms → Nat)

#whatwg_freeze (@Transform.Algorithms.cancel :
  Transform.Algorithms → Nat)

#whatwg_freeze (@Transform.Completion :
  Type)

#whatwg_freeze (@Transform.Completion.direct :
  Transform.Completion)

#whatwg_freeze (@Transform.Completion.adopt :
  Nat → Transform.Completion)

#whatwg_freeze (@Transform.Reaction :
  Type → Type)

#whatwg_freeze (@Transform.Reaction.write :
  ∀ {α : Type}, Nat → α → Nat → Transform.Reaction α)

#whatwg_freeze (@Transform.Reaction.transform :
  ∀ {α : Type}, Nat → Transform.Reaction α)

#whatwg_freeze (@Transform.Reaction.adopt :
  ∀ {α : Type}, Nat → Transform.Reaction α)

#whatwg_freeze (@Transform.Subscription :
  Type → Type)

#whatwg_freeze (@Transform.Subscription.readable :
  ∀ {α : Type}, Nat → Transform.Subscription α)

#whatwg_freeze (@Transform.Subscription.writable :
  ∀ {α : Type}, Nat → Nat → Transform.Subscription α)

#whatwg_freeze (@Transform.Subscription.reaction :
  ∀ {α : Type}, Nat → Transform.Reaction α → Transform.Subscription α)

#whatwg_freeze (@Transform.subscriptionPromise :
  ∀ {α : Type}, Transform.Subscription α → Nat)

#whatwg_freeze (@Transform.Job :
  Type → Type → Type)

#whatwg_freeze (@Transform.Job.readable :
  ∀ {α ε : Type}, Nat → Transform.Job α ε)

#whatwg_freeze (@Transform.Job.writable :
  ∀ {α ε : Type}, Nat → Transform.Job α ε)

#whatwg_freeze (@Transform.Job.reaction :
  ∀ {α ε : Type}, Transform.Reaction α → Readable.PullAnswer ε → Transform.Job α ε)

#whatwg_freeze (@Transform.Control :
  Type → Type)

#whatwg_freeze (@Transform.Control.awaitTransform :
  ∀ {ε : Type}, Nat → Transform.Completion → Nat → Transform.Control ε)

#whatwg_freeze (@Transform.Control.errorWritable :
  ∀ {ε : Type}, Boundary.Exception ε → Transform.Control ε)

#whatwg_freeze (@Transform.Control.waitWritable :
  ∀ {ε : Type}, Nat → Transform.Control ε)

#whatwg_freeze (@Transform.Control.unblock :
  ∀ {ε : Type}, Transform.Control ε)

#whatwg_freeze (@Transform.Control.settle :
  ∀ {ε : Type}, Nat → Readable.PullAnswer ε → Transform.Control ε)

#whatwg_freeze (@Transform.Event :
  Type → Type → Type → Type)

#whatwg_freeze (@Transform.Event.readable :
  ∀ {α β ε : Type}, Readable.Event β ε → Transform.Event α β ε)

#whatwg_freeze (@Transform.Event.writable :
  ∀ {α β ε : Type}, Writable.Event α ε → Transform.Event α β ε)

#whatwg_freeze (@Transform.Event.transformCalled :
  ∀ {α β ε : Type}, Nat → Nat → α → Transform.Event α β ε)

#whatwg_freeze (@Transform.Event.transformReturned :
  ∀ {α β ε : Type}, Nat → Nat → Transform.Event α β ε)

#whatwg_freeze (@Transform.Event.enqueueReturned :
  ∀ {α β ε : Type}, Nat → Except (Boundary.Exception ε) Unit → Transform.Event α β ε)

#whatwg_freeze (@Transform.State :
  Type → Type → Type → Type)

#whatwg_freeze (@Transform.State.mk :
  ∀ {α β ε : Type}, Readable.State β ε → Writable.State α ε → Transform.Ports → Bool → Nat → List
    Nat → Option Transform.Algorithms → List (Transform.Subscription α) → List (Transform.Job α
    ε) → List (Transform.Control ε) → List (Nat × Nat) → Nat → List (Transform.Event α β ε) →
    Transform.State α β ε)

#whatwg_freeze (@Transform.State.readable :
  ∀ {α β ε : Type}, Transform.State α β ε → Readable.State β ε)

#whatwg_freeze (@Transform.State.writable :
  ∀ {α β ε : Type}, Transform.State α β ε → Writable.State α ε)

#whatwg_freeze (@Transform.State.ports :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Ports)

#whatwg_freeze (@Transform.State.backpressure :
  ∀ {α β ε : Type}, Transform.State α β ε → Bool)

#whatwg_freeze (@Transform.State.backpressurePromise :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat)

#whatwg_freeze (@Transform.State.internalPromises :
  ∀ {α β ε : Type}, Transform.State α β ε → List Nat)

#whatwg_freeze (@Transform.State.algorithms :
  ∀ {α β ε : Type}, Transform.State α β ε → Option Transform.Algorithms)

#whatwg_freeze (@Transform.State.subscriptions :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Transform.Subscription α))

#whatwg_freeze (@Transform.State.jobs :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Transform.Job α ε))

#whatwg_freeze (@Transform.State.control :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Transform.Control ε))

#whatwg_freeze (@Transform.State.pendingTransforms :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Nat × Nat))

#whatwg_freeze (@Transform.State.nextCall :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat)

#whatwg_freeze (@Transform.State.trace :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Transform.Event α β ε))

#whatwg_freeze (@Transform.withReadable :
  ∀ {α β ε : Type}, Transform.State α β ε → Readable.State β ε → Transform.State α β ε)

#whatwg_freeze (@Transform.withWritable :
  ∀ {α β ε : Type}, Transform.State α β ε → Writable.State α ε → Transform.State α β ε)

#whatwg_freeze (@Transform.freshInternal :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.State α β ε × Nat)

#whatwg_freeze (@Transform.lookupPromise :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat → Option (Readable.PromiseState Unit ε))

#whatwg_freeze (@Transform.notify :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Subscription α → Readable.PullAnswer ε →
    Option (Transform.State α β ε))

#whatwg_freeze (@Transform.subscribe :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Subscription α → Option (Transform.State α
    β ε))

#whatwg_freeze (@Transform.settle :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat → Readable.PullAnswer ε → Option (Transform.State
    α β ε))

#whatwg_freeze (@Transform.setBackpressure :
  ∀ {α β ε : Type}, Transform.State α β ε → Bool → Option (Transform.State α β ε))

#whatwg_freeze (@Transform.unblockWrite :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#whatwg_freeze (@Transform.sourcePull :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε × Nat))

#whatwg_freeze (@Transform.servicePull :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#whatwg_freeze (@Transform.sinkWrite :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#whatwg_freeze (@Transform.performTransform :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat → α → Transform.Completion → Option
    (Transform.State α β ε))

#whatwg_freeze (@Transform.returnTransform :
  ∀ {α β ε : Type}, Transform.State α β ε → Readable.PullReturn ε → Option (Transform.State α β
    ε))

#whatwg_freeze (@Transform.answerTransform :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat → Readable.PullAnswer ε → Option (Transform.State
    α β ε))

#whatwg_freeze (@Transform.read :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#whatwg_freeze (@Transform.enqueue :
  ∀ {α β ε : Type}, Transform.State α β ε → β → Option (Transform.State α β ε))

#whatwg_freeze (@Transform.error :
  ∀ {α β ε : Type}, Transform.State α β ε → Boundary.Exception ε → Transform.State α β ε)

#whatwg_freeze (@Transform.terminate :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.State α β ε)

#whatwg_freeze (@Transform.react :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Reaction α → Readable.PullAnswer ε → Option
    (Transform.State α β ε))

#whatwg_freeze (@Transform.runJob :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Job α ε → Option (Transform.State α β ε))

#whatwg_freeze (@Transform.externalFrontier :
  ∀ {α β ε : Type}, Transform.State α β ε → Bool)

#whatwg_freeze (@Transform.initial :
  ∀ {α β ε : Type}, Data.DyadicSize → Data.DyadicSize → Data.SizeAlgorithm Nat → Transform.Ports
    → Transform.Algorithms → Nat → Nat → Transform.State α β ε)

#whatwg_freeze (@Transform.Decision :
  Type → Type → Type → Type)

#whatwg_freeze (@Transform.Decision.read :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.terminate :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.desiredSize :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.ready :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.closed :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.writerDesiredSize :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.enqueue :
  ∀ {α β ε : Type}, β → Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.write :
  ∀ {α β ε : Type}, α → Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.error :
  ∀ {α β ε : Type}, Boundary.Exception ε → Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.returnSize :
  ∀ {α β ε : Type}, Data.SizeAnswer Data.DyadicSize (Boundary.Exception ε) → Transform.Decision α
    β ε)

#whatwg_freeze (@Transform.Decision.returnTransform :
  ∀ {α β ε : Type}, Readable.PullReturn ε → Transform.Decision α β ε)

#whatwg_freeze (@Transform.Decision.answerTransform :
  ∀ {α β ε : Type}, Nat → Readable.PullAnswer ε → Transform.Decision α β ε)

#whatwg_freeze (@Transform.decide :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Decision α β ε → Option (Transform.State α
    β ε))

#whatwg_freeze (@Transform.tick :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#whatwg_freeze (@Transform.Step :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.Decision α β ε) → Transform.State α
    β ε → Prop)

#whatwg_freeze (@Transform.Reaches :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Option (Transform.Decision α β ε)) →
    Transform.State α β ε → Prop)

#whatwg_freeze (@Transform.OutputObservation :
  Type → Type → Type)

#whatwg_freeze (@Transform.OutputObservation.mk :
  ∀ {β ε : Type}, List β → Readable.Status ε → Writable.Status ε → Transform.OutputObservation β
    ε)

#whatwg_freeze (@Transform.OutputObservation.chunks :
  ∀ {β ε : Type}, Transform.OutputObservation β ε → List β)

#whatwg_freeze (@Transform.OutputObservation.readableStatus :
  ∀ {β ε : Type}, Transform.OutputObservation β ε → Readable.Status ε)

#whatwg_freeze (@Transform.OutputObservation.writableStatus :
  ∀ {β ε : Type}, Transform.OutputObservation β ε → Writable.Status ε)

#whatwg_freeze (@Transform.VisibleEvent :
  Type → Type → Type)

#whatwg_freeze (@Transform.VisibleEvent.readableSettlement :
  ∀ {β ε : Type}, Readable.Settlement β ε → Transform.VisibleEvent β ε)

#whatwg_freeze (@Transform.VisibleEvent.readableDesiredSize :
  ∀ {β ε : Type}, Option Readable.Size → Transform.VisibleEvent β ε)

#whatwg_freeze (@Transform.VisibleEvent.writable :
  ∀ {β ε : Type}, Writable.VisibleEvent ε → Transform.VisibleEvent β ε)

#whatwg_freeze (@Transform.VisibleEvent.enqueueReturned :
  ∀ {β ε : Type}, Nat → Except (Boundary.Exception ε) Unit → Transform.VisibleEvent β ε)

#whatwg_freeze (@Transform.OrderedObservation :
  Type → Type → Type)

#whatwg_freeze (@Transform.OrderedObservation.mk :
  ∀ {β ε : Type}, Transform.OutputObservation β ε → List (Transform.VisibleEvent β ε) →
    Transform.OrderedObservation β ε)

#whatwg_freeze (@Transform.OrderedObservation.output :
  ∀ {β ε : Type}, Transform.OrderedObservation β ε → Transform.OutputObservation β ε)

#whatwg_freeze (@Transform.OrderedObservation.events :
  ∀ {β ε : Type}, Transform.OrderedObservation β ε → List (Transform.VisibleEvent β ε))

#whatwg_freeze (@Transform.visibleEvent :
  ∀ {α β ε : Type}, List Nat → Transform.Event α β ε → Option (Transform.VisibleEvent β ε))

#whatwg_freeze (@Transform.observeOutput :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.OutputObservation β ε)

#whatwg_freeze (@Transform.observeOrdered :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.OrderedObservation β ε)
