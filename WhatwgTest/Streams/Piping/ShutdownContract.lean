import Whatwg.Streams

/-!
P7a breaker interface, 2026-09-05. Freeze state and receipts: owning contract.
PIPING-PG-FORWARD-SHUTDOWN: post-read batch, actual P4/P5 components,
independent requirements over canonical snapshots, live finalization frontier.
-/

set_option autoImplicit false

#check (@Whatwg.Streams.Piping.WriteStage :
  Type)

#check (@Whatwg.Streams.Piping.WriteStage.unwritten :
  Whatwg.Streams.Piping.WriteStage)

#check (@Whatwg.Streams.Piping.WriteStage.invoking :
  Nat → Whatwg.Streams.Piping.WriteStage)

#check (@Whatwg.Streams.Piping.WriteStage.submitted :
  Nat → Nat → Whatwg.Streams.Piping.WriteStage)

#check (@Whatwg.Streams.Piping.ReadWriteLink :
  Type → Type)

#check (@Whatwg.Streams.Piping.ReadWriteLink.mk :
  ∀ {α : Type}, Nat → α → Whatwg.Streams.Piping.WriteStage → Whatwg.Streams.Piping.ReadWriteLink α)

#check (@Whatwg.Streams.Piping.ReadWriteLink.readId :
  ∀ {α : Type}, Whatwg.Streams.Piping.ReadWriteLink α → Nat)

#check (@Whatwg.Streams.Piping.ReadWriteLink.chunk :
  ∀ {α : Type}, Whatwg.Streams.Piping.ReadWriteLink α → α)

#check (@Whatwg.Streams.Piping.ReadWriteLink.write :
  ∀ {α : Type}, Whatwg.Streams.Piping.ReadWriteLink α → Whatwg.Streams.Piping.WriteStage)

#check (@Whatwg.Streams.Piping.ShutdownPlan :
  Type → Type)

#check (@Whatwg.Streams.Piping.ShutdownPlan.mk :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε → Bool → Bool → Whatwg.Streams.Piping.ShutdownPlan ε)

#check (@Whatwg.Streams.Piping.ShutdownPlan.reason :
  ∀ {ε : Type}, Whatwg.Streams.Piping.ShutdownPlan ε → Whatwg.Streams.Boundary.Exception ε)

#check (@Whatwg.Streams.Piping.ShutdownPlan.drainRequired :
  ∀ {ε : Type}, Whatwg.Streams.Piping.ShutdownPlan ε → Bool)

#check (@Whatwg.Streams.Piping.ShutdownPlan.preventAbort :
  ∀ {ε : Type}, Whatwg.Streams.Piping.ShutdownPlan ε → Bool)

#check (@Whatwg.Streams.Piping.Snapshot :
  Type → Type → Type)

#check (@Whatwg.Streams.Piping.Snapshot.mk :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Writable.State α ε → List (Whatwg.Streams.Piping.ReadWriteLink α) → Bool → Option (Whatwg.Streams.Piping.ShutdownPlan ε) → Option Nat → Option Nat → Option (Whatwg.Streams.Boundary.Exception ε) → Whatwg.Streams.Piping.Snapshot α ε)

#check (@Whatwg.Streams.Piping.Snapshot.source :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Piping.Snapshot.destination :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Whatwg.Streams.Writable.State α ε)

#check (@Whatwg.Streams.Piping.Snapshot.links :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → List (Whatwg.Streams.Piping.ReadWriteLink α))

#check (@Whatwg.Streams.Piping.Snapshot.preventAbort :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Bool)

#check (@Whatwg.Streams.Piping.Snapshot.selection :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Option (Whatwg.Streams.Piping.ShutdownPlan ε))

#check (@Whatwg.Streams.Piping.Snapshot.abortCall :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Option Nat)

#check (@Whatwg.Streams.Piping.Snapshot.abortPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Option Nat)

#check (@Whatwg.Streams.Piping.Snapshot.finalization :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Option (Whatwg.Streams.Boundary.Exception ε))

#check (@Whatwg.Streams.Piping.ProtocolEvent :
  Type → Type → Type)

#check (@Whatwg.Streams.Piping.ProtocolEvent.selected :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ShutdownPlan ε → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolEvent.writeInvoked :
  ∀ {α ε : Type}, Nat → α → Nat → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolEvent.writeReturned :
  ∀ {α ε : Type}, Nat → Nat → Nat → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolEvent.abortInvoked :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolEvent.abortReturned :
  ∀ {α ε : Type}, Nat → Nat → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolEvent.readyToFinalize :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolEvent.writable :
  ∀ {α ε : Type}, Option (Whatwg.Streams.Writable.Decision α ε) → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolEvent.sourceError :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolEvent.administrative :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolRecord :
  Type → Type → Type)

#check (@Whatwg.Streams.Piping.ProtocolRecord.mk :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Whatwg.Streams.Piping.ProtocolEvent α ε → Whatwg.Streams.Piping.Snapshot α ε → Whatwg.Streams.Piping.ProtocolRecord α ε)

#check (@Whatwg.Streams.Piping.ProtocolRecord.before :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ProtocolRecord α ε → Whatwg.Streams.Piping.Snapshot α ε)

#check (@Whatwg.Streams.Piping.ProtocolRecord.event :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ProtocolRecord α ε → Whatwg.Streams.Piping.ProtocolEvent α ε)

#check (@Whatwg.Streams.Piping.ProtocolRecord.after :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ProtocolRecord α ε → Whatwg.Streams.Piping.Snapshot α ε)

#check (@Whatwg.Streams.Piping.ShutdownObservation :
  Type → Type → Type)

#check (@Whatwg.Streams.Piping.ShutdownObservation.mk :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → List (Whatwg.Streams.Piping.ProtocolRecord α ε) → Whatwg.Streams.Piping.Snapshot α ε → Whatwg.Streams.Piping.ShutdownObservation α ε)

#check (@Whatwg.Streams.Piping.ShutdownObservation.initial :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ShutdownObservation α ε → Whatwg.Streams.Piping.Snapshot α ε)

#check (@Whatwg.Streams.Piping.ShutdownObservation.records :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ShutdownObservation α ε → List (Whatwg.Streams.Piping.ProtocolRecord α ε))

#check (@Whatwg.Streams.Piping.ShutdownObservation.current :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ShutdownObservation α ε → Whatwg.Streams.Piping.Snapshot α ε)

#check (@Whatwg.Streams.Piping.deliveredReads :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List (Nat × α))

#check (@Whatwg.Streams.Piping.markWrite :
  ∀ {α : Type}, List (Whatwg.Streams.Piping.ReadWriteLink α) → Nat → Whatwg.Streams.Piping.WriteStage → List (Whatwg.Streams.Piping.ReadWriteLink α))

#check (@Whatwg.Streams.Piping.WritesSettled :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Prop)

#check (@Whatwg.Streams.Piping.BodyDecision :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Decision α ε → Prop)

#check (@Whatwg.Streams.Piping.ReadInventory :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Prop)

#check (@Whatwg.Streams.Piping.InitialSnapshot :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → Prop)

#check (@Whatwg.Streams.Piping.RecordAllowed :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ProtocolRecord α ε → Prop)

#check (@Whatwg.Streams.Piping.ObservationChain :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.Snapshot α ε → List (Whatwg.Streams.Piping.ProtocolRecord α ε) → Whatwg.Streams.Piping.Snapshot α ε → Prop)

#check (@Whatwg.Streams.Piping.ForwardShutdownSpec :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.ShutdownObservation α ε → Prop)

#check (@Whatwg.Streams.Piping.Phase :
  Type → Type)

#check (@Whatwg.Streams.Piping.Phase.running :
  ∀ {ε : Type}, Whatwg.Streams.Piping.Phase ε)

#check (@Whatwg.Streams.Piping.Phase.draining :
  ∀ {ε : Type}, Whatwg.Streams.Piping.Phase ε)

#check (@Whatwg.Streams.Piping.Phase.returningWrite :
  ∀ {ε : Type}, Nat → Nat → Whatwg.Streams.Piping.Phase ε)

#check (@Whatwg.Streams.Piping.Phase.waitingWrites :
  ∀ {ε : Type}, Whatwg.Streams.Piping.Phase ε)

#check (@Whatwg.Streams.Piping.Phase.returningAbort :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Piping.Phase ε)

#check (@Whatwg.Streams.Piping.Phase.waitingAbort :
  ∀ {ε : Type}, Whatwg.Streams.Piping.Phase ε)

#check (@Whatwg.Streams.Piping.Phase.readyToFinalize :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Piping.Phase ε)

#check (@Whatwg.Streams.Piping.State :
  Type → Type → Type)

#check (@Whatwg.Streams.Piping.State.mk :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Writable.State α ε → List (Whatwg.Streams.Piping.ReadWriteLink α) → Bool → Option (Whatwg.Streams.Piping.ShutdownPlan ε) → Option Nat → Option Nat → Whatwg.Streams.Piping.Phase ε → Whatwg.Streams.Piping.Snapshot α ε → List (Whatwg.Streams.Piping.ProtocolRecord α ε) → Whatwg.Streams.Piping.State α ε)

#check (@Whatwg.Streams.Piping.State.source :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Piping.State.destination :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Writable.State α ε)

#check (@Whatwg.Streams.Piping.State.links :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → List (Whatwg.Streams.Piping.ReadWriteLink α))

#check (@Whatwg.Streams.Piping.State.preventAbort :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Bool)

#check (@Whatwg.Streams.Piping.State.selection :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Option (Whatwg.Streams.Piping.ShutdownPlan ε))

#check (@Whatwg.Streams.Piping.State.abortCall :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Option Nat)

#check (@Whatwg.Streams.Piping.State.abortPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Option Nat)

#check (@Whatwg.Streams.Piping.State.phase :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.Phase ε)

#check (@Whatwg.Streams.Piping.State.entry :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.Snapshot α ε)

#check (@Whatwg.Streams.Piping.State.trace :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → List (Whatwg.Streams.Piping.ProtocolRecord α ε))

#check (@Whatwg.Streams.Piping.initial :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Writable.State α ε → Bool → Whatwg.Streams.Piping.State α ε)

#check (@Whatwg.Streams.Piping.snapshot :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.Snapshot α ε)

#check (@Whatwg.Streams.Piping.observeShutdown :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.ShutdownObservation α ε)

#check (@Whatwg.Streams.Piping.emit :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.ProtocolEvent α ε → Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.State α ε)

#check (@Whatwg.Streams.Piping.drainGuard :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Bool)

#check (@Whatwg.Streams.Piping.nextUnwritten :
  ∀ {α : Type}, List (Whatwg.Streams.Piping.ReadWriteLink α) → Option (Whatwg.Streams.Piping.ReadWriteLink α))

#check (@Whatwg.Streams.Piping.allWrittenSettled :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List (Whatwg.Streams.Piping.ReadWriteLink α) → Bool)

#check (@Whatwg.Streams.Piping.lookupReturn :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat → Option Nat)

#check (@Whatwg.Streams.Piping.foreignDecision :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Decision α ε → Bool)

#check (@Whatwg.Streams.Piping.enterForwardShutdown :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.State α ε)

#check (@Whatwg.Streams.Piping.invokeWrite :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.ReadWriteLink α → Option (Whatwg.Streams.Piping.State α ε))

#check (@Whatwg.Streams.Piping.captureWrite :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Nat → Nat → Option (Whatwg.Streams.Piping.State α ε))

#check (@Whatwg.Streams.Piping.invokeAbort :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.ShutdownPlan ε → Option (Whatwg.Streams.Piping.State α ε))

#check (@Whatwg.Streams.Piping.captureAbort :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Nat → Option (Whatwg.Streams.Piping.State α ε))

#check (@Whatwg.Streams.Piping.requestFinalize :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Piping.State α ε)

#check (@Whatwg.Streams.Piping.stepWritable :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Option (Whatwg.Streams.Writable.Decision α ε) → Option (Whatwg.Streams.Piping.State α ε))

#check (@Whatwg.Streams.Piping.externalFrontier :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Bool)

#check (@Whatwg.Streams.Piping.Decision :
  Type → Type → Type)

#check (@Whatwg.Streams.Piping.Decision.sourceError :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Piping.Decision α ε)

#check (@Whatwg.Streams.Piping.Decision.writable :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Decision α ε → Whatwg.Streams.Piping.Decision α ε)

#check (@Whatwg.Streams.Piping.decide :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Whatwg.Streams.Piping.Decision α ε → Option (Whatwg.Streams.Piping.State α ε))

#check (@Whatwg.Streams.Piping.tick :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Option (Whatwg.Streams.Piping.State α ε))

#check (@Whatwg.Streams.Piping.Step :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Option (Whatwg.Streams.Piping.Decision α ε) → Whatwg.Streams.Piping.State α ε → Prop)

#check (@Whatwg.Streams.Piping.Reaches :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → List (Option (Whatwg.Streams.Piping.Decision α ε)) → Whatwg.Streams.Piping.State α ε → Prop)

#check (@Whatwg.Streams.Piping.Admitted :
  ∀ {α ε : Type}, Whatwg.Streams.Piping.State α ε → Prop)
