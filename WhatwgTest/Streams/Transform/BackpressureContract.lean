import Whatwg.Streams

/-! Frozen P6a exact surface, 2026-09-05.
Graph: TRANSFORM-PG-BACKPRESSURE. Count output profile; canonical P4/P5 coupling.
The symbols below are planned production declarations, never local replacement runtimes.
-/

set_option autoImplicit false
open Whatwg.Streams

#check (@Transform.Ports :
  Type)

#check (@Transform.Ports.mk :
  Nat → Nat → Nat → Nat → Nat → Transform.Ports)

#check (@Transform.Ports.pull :
  Transform.Ports → Nat)

#check (@Transform.Ports.readCancel :
  Transform.Ports → Nat)

#check (@Transform.Ports.write :
  Transform.Ports → Nat)

#check (@Transform.Ports.close :
  Transform.Ports → Nat)

#check (@Transform.Ports.abort :
  Transform.Ports → Nat)

#check (@Transform.Algorithms :
  Type)

#check (@Transform.Algorithms.mk :
  Nat → Nat → Nat → Transform.Algorithms)

#check (@Transform.Algorithms.transform :
  Transform.Algorithms → Nat)

#check (@Transform.Algorithms.flush :
  Transform.Algorithms → Nat)

#check (@Transform.Algorithms.cancel :
  Transform.Algorithms → Nat)

#check (@Transform.Completion :
  Type)

#check (@Transform.Completion.direct :
  Transform.Completion)

#check (@Transform.Completion.adopt :
  Nat → Transform.Completion)

#check (@Transform.Reaction :
  Type → Type)

#check (@Transform.Reaction.write :
  ∀ {α : Type}, Nat → α → Nat → Transform.Reaction α)

#check (@Transform.Reaction.transform :
  ∀ {α : Type}, Nat → Transform.Reaction α)

#check (@Transform.Reaction.adopt :
  ∀ {α : Type}, Nat → Transform.Reaction α)

#check (@Transform.Subscription :
  Type → Type)

#check (@Transform.Subscription.readable :
  ∀ {α : Type}, Nat → Transform.Subscription α)

#check (@Transform.Subscription.writable :
  ∀ {α : Type}, Nat → Nat → Transform.Subscription α)

#check (@Transform.Subscription.reaction :
  ∀ {α : Type}, Nat → Transform.Reaction α → Transform.Subscription α)

#check (@Transform.subscriptionPromise :
  ∀ {α : Type}, Transform.Subscription α → Nat)

#check (@Transform.Job :
  Type → Type → Type)

#check (@Transform.Job.readable :
  ∀ {α ε : Type}, Nat → Transform.Job α ε)

#check (@Transform.Job.writable :
  ∀ {α ε : Type}, Nat → Transform.Job α ε)

#check (@Transform.Job.reaction :
  ∀ {α ε : Type}, Transform.Reaction α → Readable.PullAnswer ε → Transform.Job α ε)

#check (@Transform.Control :
  Type → Type)

#check (@Transform.Control.awaitTransform :
  ∀ {ε : Type}, Nat → Transform.Completion → Nat → Transform.Control ε)

#check (@Transform.Control.errorWritable :
  ∀ {ε : Type}, Boundary.Exception ε → Transform.Control ε)

#check (@Transform.Control.waitWritable :
  ∀ {ε : Type}, Nat → Transform.Control ε)

#check (@Transform.Control.unblock :
  ∀ {ε : Type}, Transform.Control ε)

#check (@Transform.Control.settle :
  ∀ {ε : Type}, Nat → Readable.PullAnswer ε → Transform.Control ε)

#check (@Transform.Event :
  Type → Type → Type → Type)

#check (@Transform.Event.readable :
  ∀ {α β ε : Type}, Readable.Event β ε → Transform.Event α β ε)

#check (@Transform.Event.writable :
  ∀ {α β ε : Type}, Writable.Event α ε → Transform.Event α β ε)

#check (@Transform.Event.transformCalled :
  ∀ {α β ε : Type}, Nat → Nat → α → Transform.Event α β ε)

#check (@Transform.Event.transformReturned :
  ∀ {α β ε : Type}, Nat → Nat → Transform.Event α β ε)

#check (@Transform.Event.enqueueReturned :
  ∀ {α β ε : Type}, Nat → Except (Boundary.Exception ε) Unit → Transform.Event α β ε)

#check (@Transform.State :
  Type → Type → Type → Type)

#check (@Transform.State.mk :
  ∀ {α β ε : Type}, Readable.State β ε → Writable.State α ε → Transform.Ports → Bool → Nat → List
    Nat → Option Transform.Algorithms → List (Transform.Subscription α) → List (Transform.Job α
    ε) → List (Transform.Control ε) → List (Nat × Nat) → Nat → List (Transform.Event α β ε) →
    Transform.State α β ε)

#check (@Transform.State.readable :
  ∀ {α β ε : Type}, Transform.State α β ε → Readable.State β ε)

#check (@Transform.State.writable :
  ∀ {α β ε : Type}, Transform.State α β ε → Writable.State α ε)

#check (@Transform.State.ports :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Ports)

#check (@Transform.State.backpressure :
  ∀ {α β ε : Type}, Transform.State α β ε → Bool)

#check (@Transform.State.backpressurePromise :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat)

#check (@Transform.State.internalPromises :
  ∀ {α β ε : Type}, Transform.State α β ε → List Nat)

#check (@Transform.State.algorithms :
  ∀ {α β ε : Type}, Transform.State α β ε → Option Transform.Algorithms)

#check (@Transform.State.subscriptions :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Transform.Subscription α))

#check (@Transform.State.jobs :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Transform.Job α ε))

#check (@Transform.State.control :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Transform.Control ε))

#check (@Transform.State.pendingTransforms :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Nat × Nat))

#check (@Transform.State.nextCall :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat)

#check (@Transform.State.trace :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Transform.Event α β ε))

#check (@Transform.withReadable :
  ∀ {α β ε : Type}, Transform.State α β ε → Readable.State β ε → Transform.State α β ε)

#check (@Transform.withWritable :
  ∀ {α β ε : Type}, Transform.State α β ε → Writable.State α ε → Transform.State α β ε)

#check (@Transform.freshInternal :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.State α β ε × Nat)

#check (@Transform.lookupPromise :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat → Option (Readable.PromiseState Unit ε))

#check (@Transform.notify :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Subscription α → Readable.PullAnswer ε →
    Option (Transform.State α β ε))

#check (@Transform.subscribe :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Subscription α → Option (Transform.State α
    β ε))

#check (@Transform.settle :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat → Readable.PullAnswer ε → Option (Transform.State
    α β ε))

#check (@Transform.setBackpressure :
  ∀ {α β ε : Type}, Transform.State α β ε → Bool → Option (Transform.State α β ε))

#check (@Transform.unblockWrite :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#check (@Transform.sourcePull :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε × Nat))

#check (@Transform.servicePull :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#check (@Transform.sinkWrite :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#check (@Transform.performTransform :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat → α → Transform.Completion → Option
    (Transform.State α β ε))

#check (@Transform.returnTransform :
  ∀ {α β ε : Type}, Transform.State α β ε → Readable.PullReturn ε → Option (Transform.State α β
    ε))

#check (@Transform.answerTransform :
  ∀ {α β ε : Type}, Transform.State α β ε → Nat → Readable.PullAnswer ε → Option (Transform.State
    α β ε))

#check (@Transform.read :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#check (@Transform.enqueue :
  ∀ {α β ε : Type}, Transform.State α β ε → β → Option (Transform.State α β ε))

#check (@Transform.error :
  ∀ {α β ε : Type}, Transform.State α β ε → Boundary.Exception ε → Transform.State α β ε)

#check (@Transform.terminate :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.State α β ε)

#check (@Transform.react :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Reaction α → Readable.PullAnswer ε → Option
    (Transform.State α β ε))

#check (@Transform.runJob :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Job α ε → Option (Transform.State α β ε))

#check (@Transform.externalFrontier :
  ∀ {α β ε : Type}, Transform.State α β ε → Bool)

#check (@Transform.initial :
  ∀ {α β ε : Type}, Data.DyadicSize → Data.DyadicSize → Data.SizeAlgorithm Nat → Transform.Ports
    → Transform.Algorithms → Nat → Nat → Transform.State α β ε)

#check (@Transform.Decision :
  Type → Type → Type → Type)

#check (@Transform.Decision.read :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#check (@Transform.Decision.terminate :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#check (@Transform.Decision.desiredSize :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#check (@Transform.Decision.ready :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#check (@Transform.Decision.closed :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#check (@Transform.Decision.writerDesiredSize :
  ∀ {α β ε : Type}, Transform.Decision α β ε)

#check (@Transform.Decision.enqueue :
  ∀ {α β ε : Type}, β → Transform.Decision α β ε)

#check (@Transform.Decision.write :
  ∀ {α β ε : Type}, α → Transform.Decision α β ε)

#check (@Transform.Decision.error :
  ∀ {α β ε : Type}, Boundary.Exception ε → Transform.Decision α β ε)

#check (@Transform.Decision.returnSize :
  ∀ {α β ε : Type}, Data.SizeAnswer Data.DyadicSize (Boundary.Exception ε) → Transform.Decision α
    β ε)

#check (@Transform.Decision.returnTransform :
  ∀ {α β ε : Type}, Readable.PullReturn ε → Transform.Decision α β ε)

#check (@Transform.Decision.answerTransform :
  ∀ {α β ε : Type}, Nat → Readable.PullAnswer ε → Transform.Decision α β ε)

#check (@Transform.decide :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.Decision α β ε → Option (Transform.State α
    β ε))

#check (@Transform.tick :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.State α β ε))

#check (@Transform.Step :
  ∀ {α β ε : Type}, Transform.State α β ε → Option (Transform.Decision α β ε) → Transform.State α
    β ε → Prop)

#check (@Transform.Reaches :
  ∀ {α β ε : Type}, Transform.State α β ε → List (Option (Transform.Decision α β ε)) →
    Transform.State α β ε → Prop)

#check (@Transform.OutputObservation :
  Type → Type → Type)

#check (@Transform.OutputObservation.mk :
  ∀ {β ε : Type}, List β → Readable.Status ε → Writable.Status ε → Transform.OutputObservation β
    ε)

#check (@Transform.OutputObservation.chunks :
  ∀ {β ε : Type}, Transform.OutputObservation β ε → List β)

#check (@Transform.OutputObservation.readableStatus :
  ∀ {β ε : Type}, Transform.OutputObservation β ε → Readable.Status ε)

#check (@Transform.OutputObservation.writableStatus :
  ∀ {β ε : Type}, Transform.OutputObservation β ε → Writable.Status ε)

#check (@Transform.VisibleEvent :
  Type → Type → Type)

#check (@Transform.VisibleEvent.readableSettlement :
  ∀ {β ε : Type}, Readable.Settlement β ε → Transform.VisibleEvent β ε)

#check (@Transform.VisibleEvent.readableDesiredSize :
  ∀ {β ε : Type}, Option Readable.Size → Transform.VisibleEvent β ε)

#check (@Transform.VisibleEvent.writable :
  ∀ {β ε : Type}, Writable.VisibleEvent ε → Transform.VisibleEvent β ε)

#check (@Transform.VisibleEvent.enqueueReturned :
  ∀ {β ε : Type}, Nat → Except (Boundary.Exception ε) Unit → Transform.VisibleEvent β ε)

#check (@Transform.OrderedObservation :
  Type → Type → Type)

#check (@Transform.OrderedObservation.mk :
  ∀ {β ε : Type}, Transform.OutputObservation β ε → List (Transform.VisibleEvent β ε) →
    Transform.OrderedObservation β ε)

#check (@Transform.OrderedObservation.output :
  ∀ {β ε : Type}, Transform.OrderedObservation β ε → Transform.OutputObservation β ε)

#check (@Transform.OrderedObservation.events :
  ∀ {β ε : Type}, Transform.OrderedObservation β ε → List (Transform.VisibleEvent β ε))

#check (@Transform.visibleEvent :
  ∀ {α β ε : Type}, List Nat → Transform.Event α β ε → Option (Transform.VisibleEvent β ε))

#check (@Transform.observeOutput :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.OutputObservation β ε)

#check (@Transform.observeOrdered :
  ∀ {α β ε : Type}, Transform.State α β ε → Transform.OrderedObservation β ε)
