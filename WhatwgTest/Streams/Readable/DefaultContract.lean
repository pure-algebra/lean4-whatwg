import Whatwg.Streams

/-!
Breaker-owned P4a exact-signature battery. Contract: test/contracts/readable-default.contract.md.
Graph: READABLE-PG-DEFAULT. The builder must not change these statements.
Every production spelling is fully qualified. The root import is intentional: its existing stubs
are importable before implementation, so the intended red failures are unknown declarations.
Slot laws support M2, settlementTrace is its settlement component, and observeM2 includes M1.
-/

set_option autoImplicit false


/-! Shared exception adapter (P3-R2), reused numeric and first-order data surfaces. -/

#check (@Whatwg.Streams.Boundary.Exception :
  Type → Type)

#check (@Whatwg.Streams.Boundary.Exception.rangeError :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε)

#check (@Whatwg.Streams.Boundary.Exception.typeError :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε)

#check (@Whatwg.Streams.Boundary.Exception.foreign :
  ∀ {ε : Type}, ε → Whatwg.Streams.Boundary.Exception ε)

#check (@Whatwg.Streams.Boundary.Exception.ofRangeError :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Data.RangeError → Whatwg.Streams.Boundary.Exception ε)

#check (@Whatwg.Streams.Boundary.Exception.toRangeError :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε → Option Whatwg.Streams.Data.RangeError)

#check (@Whatwg.Streams.Boundary.Exception.toRangeError_ofRangeError :
  ∀ {ε : Type} (id : Nat) (e : Whatwg.Streams.Data.RangeError),
    Whatwg.Streams.Boundary.Exception.toRangeError (Whatwg.Streams.Boundary.Exception.ofRangeError
      (ε := ε) id e) = some e)

#check (@Whatwg.Streams.Boundary.Exception.toRangeError_typeError :
  ∀ {ε : Type} (id : Nat),
    Whatwg.Streams.Boundary.Exception.toRangeError (Whatwg.Streams.Boundary.Exception.typeError id
      : Whatwg.Streams.Boundary.Exception ε) = none)

#check (@Whatwg.Streams.Boundary.Exception.toRangeError_foreign :
  ∀ {ε : Type} (e : ε),
    Whatwg.Streams.Boundary.Exception.toRangeError (Whatwg.Streams.Boundary.Exception.foreign e) =
      none)

#check (@Whatwg.Streams.Boundary.Exception.ofRangeError_eq :
  ∀ {ε : Type} (id : Nat),
    Whatwg.Streams.Boundary.Exception.ofRangeError (ε := ε) id .rangeError = .rangeError id)

#check (@Whatwg.Streams.Boundary.Exception.rangeError_eq_iff :
  ∀ {ε : Type} (left right : Nat),
    (Whatwg.Streams.Boundary.Exception.rangeError left : Whatwg.Streams.Boundary.Exception ε) =
      .rangeError right ↔ left = right)

#check (@Whatwg.Streams.Readable.Size :
  Type)

#check (@Whatwg.Streams.Readable.sizes :
  Whatwg.Streams.Data.SizeClass Whatwg.Streams.Readable.Size)

#check (@Whatwg.Streams.Readable.size_eq :
  Whatwg.Streams.Readable.Size = Whatwg.Streams.Data.DyadicSize)

#check (@Whatwg.Streams.Readable.sizes_eq :
  Whatwg.Streams.Readable.sizes = Whatwg.Streams.Data.DyadicSize.sizes)

#check (@Whatwg.Streams.Readable.Status :
  Type → Type)

#check (@Whatwg.Streams.Readable.ReadResult :
  Type → Type)

#check (@Whatwg.Streams.Readable.PromiseState :
  Type → Type → Type)

#check (@Whatwg.Streams.Readable.Algorithms :
  Type)

#check (@Whatwg.Streams.Readable.Settlement :
  Type → Type → Type)

#check (@Whatwg.Streams.Readable.Event :
  Type → Type → Type)

#check (@Whatwg.Streams.Readable.Frame :
  Type → Type)

#check (@Whatwg.Streams.Readable.PullAnswer :
  Type → Type)

#check (@Whatwg.Streams.Readable.State :
  Type → Type → Type)

#check (@Whatwg.Streams.Readable.Decision :
  Type → Type → Type)

#check (@Whatwg.Streams.Readable.Status.readable :
  ∀ {ε : Type}, Whatwg.Streams.Readable.Status ε)

#check (@Whatwg.Streams.Readable.Status.closed :
  ∀ {ε : Type}, Whatwg.Streams.Readable.Status ε)

#check (@Whatwg.Streams.Readable.Status.errored :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Readable.Status ε)

#check (@Whatwg.Streams.Readable.ReadResult.chunk :
  ∀ {α : Type}, α → Whatwg.Streams.Readable.ReadResult α)

#check (@Whatwg.Streams.Readable.ReadResult.done :
  ∀ {α : Type}, Whatwg.Streams.Readable.ReadResult α)

#check (@Whatwg.Streams.Readable.PromiseState.pending :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.PromiseState α ε)

#check (@Whatwg.Streams.Readable.PromiseState.fulfilled :
  ∀ {α ε : Type}, α → Whatwg.Streams.Readable.PromiseState α ε)

#check (@Whatwg.Streams.Readable.PromiseState.rejected :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Readable.PromiseState α ε)

#check (@Whatwg.Streams.Readable.Algorithms.mk :
  Whatwg.Streams.Data.SizeAlgorithm Nat → Nat → Nat → Whatwg.Streams.Readable.Algorithms)

#check (@Whatwg.Streams.Readable.Algorithms.size :
  Whatwg.Streams.Readable.Algorithms → Whatwg.Streams.Data.SizeAlgorithm Nat)

#check (@Whatwg.Streams.Readable.Algorithms.pull :
  Whatwg.Streams.Readable.Algorithms → Nat)

#check (@Whatwg.Streams.Readable.Algorithms.cancel :
  Whatwg.Streams.Readable.Algorithms → Nat)

#check (@Whatwg.Streams.Readable.Settlement.closed :
  ∀ {α ε : Type}, Except (Whatwg.Streams.Boundary.Exception ε) Unit →
    Whatwg.Streams.Readable.Settlement α ε)

#check (@Whatwg.Streams.Readable.Settlement.read :
  ∀ {α ε : Type}, Nat → Except (Whatwg.Streams.Boundary.Exception ε)
    (Whatwg.Streams.Readable.ReadResult α) →
    Whatwg.Streams.Readable.Settlement α ε)

#check (@Whatwg.Streams.Readable.Event.sizeCalled :
  ∀ {α ε : Type}, Nat → Nat → α → Whatwg.Streams.Readable.Event α ε)

#check (@Whatwg.Streams.Readable.Event.pullCalled :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Readable.Event α ε)

#check (@Whatwg.Streams.Readable.Event.enqueueReturned :
  ∀ {α ε : Type}, Nat → Except (Whatwg.Streams.Boundary.Exception ε) Unit →
    Whatwg.Streams.Readable.Event α ε)

#check (@Whatwg.Streams.Readable.Event.settled :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.Settlement α ε → Whatwg.Streams.Readable.Event α ε)

#check (@Whatwg.Streams.Readable.PullAnswer.fulfilled :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PullAnswer ε)

#check (@Whatwg.Streams.Readable.PullAnswer.rejected :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Readable.PullAnswer ε)

#check (@Whatwg.Streams.Readable.State.mk :
  ∀ {α ε : Type},
    Whatwg.Streams.Readable.Status ε →
    Whatwg.Streams.Data.Queue α Whatwg.Streams.Readable.Size →
    Whatwg.Streams.Readable.Size →
    Bool →
    Bool →
    Bool →
    Bool →
    Option Whatwg.Streams.Readable.Algorithms →
    List Nat →
    Nat →
    Nat →
    Nat →
    Whatwg.Streams.Readable.PromiseState Unit ε →
    List (Nat × Whatwg.Streams.Readable.PromiseState (Whatwg.Streams.Readable.ReadResult α) ε) →
    List (Whatwg.Streams.Readable.Frame α) →
    Bool →
    List (Whatwg.Streams.Readable.PullAnswer ε) →
    List (Whatwg.Streams.Readable.Event α ε) → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.State.status :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.Status ε)

#check (@Whatwg.Streams.Readable.State.queue :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Data.Queue α
    Whatwg.Streams.Readable.Size)

#check (@Whatwg.Streams.Readable.State.highWaterMark :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.Size)

#check (@Whatwg.Streams.Readable.State.started :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Bool)

#check (@Whatwg.Streams.Readable.State.closeRequested :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Bool)

#check (@Whatwg.Streams.Readable.State.pulling :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Bool)

#check (@Whatwg.Streams.Readable.State.pullAgain :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Bool)

#check (@Whatwg.Streams.Readable.State.algorithms :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Option Whatwg.Streams.Readable.Algorithms)

#check (@Whatwg.Streams.Readable.State.readRequests :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List Nat)

#check (@Whatwg.Streams.Readable.State.nextRead :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Nat)

#check (@Whatwg.Streams.Readable.State.nextEnqueue :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Nat)

#check (@Whatwg.Streams.Readable.State.closedPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.PromiseState Unit ε)

#check (@Whatwg.Streams.Readable.State.readPromises :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List (Nat ×
    Whatwg.Streams.Readable.PromiseState (Whatwg.Streams.Readable.ReadResult α) ε))

#check (@Whatwg.Streams.Readable.State.frames :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List (Whatwg.Streams.Readable.Frame α))

#check (@Whatwg.Streams.Readable.State.pullAwaiting :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Bool)

#check (@Whatwg.Streams.Readable.State.jobs :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List (Whatwg.Streams.Readable.PullAnswer ε))

#check (@Whatwg.Streams.Readable.State.trace :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List (Whatwg.Streams.Readable.Event α ε))


/-! Total abstract-operation and observation signatures. Unknown answers are frontiers. -/

#check (@Whatwg.Streams.Readable.initial :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.Algorithms → Whatwg.Streams.Readable.Size →
    Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.sizePositive :
  Whatwg.Streams.Readable.Size → Bool)

#check (@Whatwg.Streams.Readable.canCloseOrEnqueue :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Bool)

#check (@Whatwg.Streams.Readable.shouldCallPull :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Bool)

#check (@Whatwg.Streams.Readable.desiredSize :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Option Whatwg.Streams.Readable.Size)

#check (@Whatwg.Streams.Readable.callPullIfNeeded :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.close :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.read :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.error :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Boundary.Exception ε →
    Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.beginEnqueue :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → α → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.finishEnqueue :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Nat → α →
    Whatwg.Streams.Data.SizeAnswer Whatwg.Streams.Readable.Size (Whatwg.Streams.Boundary.Exception
      ε) → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.resumeSize :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε →
    Whatwg.Streams.Data.SizeAnswer Whatwg.Streams.Readable.Size (Whatwg.Streams.Boundary.Exception
      ε) → Option (Whatwg.Streams.Readable.State α ε))

#check (@Whatwg.Streams.Readable.acceptPullAnswer :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.PullAnswer ε →
    Option (Whatwg.Streams.Readable.State α ε))

#check (@Whatwg.Streams.Readable.reactPull :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.PullAnswer ε →
    Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.runPullJob :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Option (Whatwg.Streams.Readable.State α ε))

#check (@Whatwg.Streams.Readable.settlementTrace :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List (Whatwg.Streams.Readable.Settlement α ε))

#check (@Whatwg.Streams.Readable.chunksOfSettlements :
  ∀ {α ε : Type}, List (Whatwg.Streams.Readable.Settlement α ε) → List α)

#check (@Whatwg.Streams.Readable.observeM1 :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List α × Whatwg.Streams.Readable.Status ε)


/-! Construction, numerical and demand equations. Structural slot laws under M2. -/

#check (@Whatwg.Streams.Readable.initial_eq :
  ∀ {α ε : Type} (algorithms : Whatwg.Streams.Readable.Algorithms) (hwm :
    Whatwg.Streams.Readable.Size),
    Whatwg.Streams.Readable.initial (α := α) (ε := ε) algorithms hwm =
      { status := .readable, queue := Whatwg.Streams.Data.Queue.empty
        Whatwg.Streams.Readable.sizes, highWaterMark := hwm,
        started := true, closeRequested := false, pulling := false, pullAgain := false,
        algorithms := some algorithms, readRequests := [], nextRead := 0, nextEnqueue := 0,
          nextError := 0,
        closedPromise := .pending, readPromises := [], frames := [], pullAwaiting := false,
        jobs := [], trace := [] })

#check (@Whatwg.Streams.Readable.sizePositive_eq :
  ∀ (v : Whatwg.Streams.Readable.Size), Whatwg.Streams.Readable.sizePositive v =
    match v with
    | .posInfinity => true
    | .finite units => decide (0 < units)
    | _ => false)

#check (@Whatwg.Streams.Readable.desiredSize_readable :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε), s.status = .readable →
    Whatwg.Streams.Readable.desiredSize s = some (Whatwg.Streams.Readable.sizes.sub s.highWaterMark
      s.queue.totalSize))

#check (@Whatwg.Streams.Readable.desiredSize_closed :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε), s.status = .closed →
    Whatwg.Streams.Readable.desiredSize s = some Whatwg.Streams.Readable.sizes.zero)

#check (@Whatwg.Streams.Readable.desiredSize_errored :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    s.status = .errored e → Whatwg.Streams.Readable.desiredSize s = none)

#check (@Whatwg.Streams.Readable.canCloseOrEnqueue_iff :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.canCloseOrEnqueue s = true ↔ s.status = .readable ∧ s.closeRequested =
      false)

#check (@Whatwg.Streams.Readable.shouldCallPull_iff :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.shouldCallPull s = true ↔
      s.status = .readable ∧ s.closeRequested = false ∧ s.started = true ∧
        (s.readRequests ≠ [] ∨
          Whatwg.Streams.Readable.sizePositive (Whatwg.Streams.Readable.sizes.sub s.highWaterMark
            s.queue.totalSize) = true))

#check (@Whatwg.Streams.Readable.callPullIfNeeded_idle :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.shouldCallPull s = false → Whatwg.Streams.Readable.callPullIfNeeded s =
      s)

#check (@Whatwg.Streams.Readable.callPullIfNeeded_busy :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.shouldCallPull s = true → s.pulling = true →
      Whatwg.Streams.Readable.callPullIfNeeded s = { s with pullAgain := true })

#check (@Whatwg.Streams.Readable.callPullIfNeeded_start :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (a : Whatwg.Streams.Readable.Algorithms),
    Whatwg.Streams.Readable.shouldCallPull s = true → s.pulling = false → s.algorithms = some a →
      Whatwg.Streams.Readable.callPullIfNeeded s =
        { s with
          pulling := true, pullAwaiting := false, frames := .pull .done :: s.frames,
          trace := s.trace ++ [.pullCalled a.pull] })

#check (@Whatwg.Streams.Readable.callPullIfNeeded_missing :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.shouldCallPull s = true → s.pulling = false → s.algorithms = none →
      Whatwg.Streams.Readable.callPullIfNeeded s = s)


/-! Foreign answers and FIFO reaction jobs. M2 execution order; no response is no transition. -/

#check (@Whatwg.Streams.Readable.acceptPullAnswer_waiting :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (a : Whatwg.Streams.Readable.PullAnswer ε),
    s.pullAwaiting = true → Whatwg.Streams.Readable.acceptPullAnswer s a =
      some { s with pullAwaiting := false, jobs := s.jobs ++ [a] })

#check (@Whatwg.Streams.Readable.acceptPullAnswer_unmatched :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (a : Whatwg.Streams.Readable.PullAnswer ε),
    s.pullAwaiting = false → Whatwg.Streams.Readable.acceptPullAnswer s a = none)

#check (@Whatwg.Streams.Readable.reactPull_fulfilled :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.reactPull s .fulfilled =
      if s.pullAgain then
        Whatwg.Streams.Readable.callPullIfNeeded
          { s with pulling := false, pullAgain := false }
      else { s with pulling := false })

#check (@Whatwg.Streams.Readable.reactPull_rejected :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Readable.reactPull s (.rejected e) = Whatwg.Streams.Readable.error s e)

#check (@Whatwg.Streams.Readable.runPullJob_suspended :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    s.frames ≠ [] → Whatwg.Streams.Readable.runPullJob s = none)

#check (@Whatwg.Streams.Readable.runPullJob_empty :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    s.jobs = [] → Whatwg.Streams.Readable.runPullJob s = none)

#check (@Whatwg.Streams.Readable.runPullJob_cons :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (a : Whatwg.Streams.Readable.PullAnswer ε)
    (rest : List (Whatwg.Streams.Readable.PullAnswer ε)),
    s.frames = [] → s.jobs = a :: rest →
      Whatwg.Streams.Readable.runPullJob s = some (Whatwg.Streams.Readable.reactPull { s with jobs
        := rest } a))


/-! Close and error preserve suspended continuations. Exact settlement-order component of M2. -/

#check (@Whatwg.Streams.Readable.close_blocked :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.canCloseOrEnqueue s = false → Whatwg.Streams.Readable.close s = s)

#check (@Whatwg.Streams.Readable.close_deferred :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.canCloseOrEnqueue s = true → s.queue.entries ≠ [] →
      Whatwg.Streams.Readable.close s = { s with closeRequested := true })

#check (@Whatwg.Streams.Readable.close_empty :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.canCloseOrEnqueue s = true → s.queue.entries = [] →
      Whatwg.Streams.Readable.close s =
        { s with
          status := .closed, closeRequested := true, algorithms := none,
          readRequests := [], closedPromise := .fulfilled (),
          readPromises := s.readPromises.map (fun p ↦
            if p.1 ∈ s.readRequests then (p.1, .fulfilled .done) else p),
          trace := s.trace ++ [.settled (.closed (.ok ()))] ++
            s.readRequests.map (fun id ↦ .settled (.read id (.ok .done))) })

#check (@Whatwg.Streams.Readable.error_terminal :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    s.status ≠ .readable → Whatwg.Streams.Readable.error s e = s)

#check (@Whatwg.Streams.Readable.error_readable :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    s.status = .readable → Whatwg.Streams.Readable.error s e =
      { s with
        status := .errored e, queue := Whatwg.Streams.Data.resetQueue Whatwg.Streams.Readable.sizes
          s.queue,
        algorithms := none, readRequests := [], closedPromise := .rejected e,
        readPromises := s.readPromises.map (fun p ↦
          if p.1 ∈ s.readRequests then (p.1, .rejected e) else p),
        trace := s.trace ++ [.settled (.closed (.error e))] ++
          s.readRequests.map (fun id ↦ .settled (.read id (.error e))) })


/-! Default-reader laws. Pull invocation suspends before chunk settlement; M1/M2 witnesses follow.
  -/

#check (@Whatwg.Streams.Readable.read_closed :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε), s.status = .closed →
    Whatwg.Streams.Readable.read s =
      { s with
        nextRead := s.nextRead + 1,
        readPromises := s.readPromises ++ [(s.nextRead, .fulfilled .done)],
        trace := s.trace ++ [.settled (.read s.nextRead (.ok .done))] })

#check (@Whatwg.Streams.Readable.read_errored :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    s.status = .errored e → Whatwg.Streams.Readable.read s =
      { s with
        nextRead := s.nextRead + 1,
        readPromises := s.readPromises ++ [(s.nextRead, .rejected e)],
        trace := s.trace ++ [.settled (.read s.nextRead (.error e))] })

#check (@Whatwg.Streams.Readable.read_empty :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    s.status = .readable → s.queue.entries = [] →
      Whatwg.Streams.Readable.read s = Whatwg.Streams.Readable.callPullIfNeeded
        { s with
          nextRead := s.nextRead + 1,
          readPromises := s.readPromises ++ [(s.nextRead, .pending)],
          readRequests := s.readRequests ++ [s.nextRead] })

#check (@Whatwg.Streams.Readable.read_nextRead :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε), (Whatwg.Streams.Readable.read s).nextRead
    = s.nextRead + 1)


/-! Staged enqueue laws. No state/delivery recheck is permitted after foreign size returns. -/

#check (@Whatwg.Streams.Readable.beginEnqueue_blocked :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (chunk : α),
    Whatwg.Streams.Readable.canCloseOrEnqueue s = false → Whatwg.Streams.Readable.beginEnqueue s
      chunk = s)

#check (@Whatwg.Streams.Readable.beginEnqueue_pending :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (chunk : α) (id : Nat)
    (rest : List Nat), Whatwg.Streams.Readable.canCloseOrEnqueue s = true → s.readRequests = id ::
      rest →
      Whatwg.Streams.Readable.beginEnqueue s chunk =
        Whatwg.Streams.Readable.callPullIfNeededWith
          { s with
            readRequests := rest, nextEnqueue := s.nextEnqueue + 1,
            readPromises := s.readPromises.map (fun p ↦
              if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p),
            trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] }
          (.returnEnqueue s.nextEnqueue))

#check (@Whatwg.Streams.Readable.beginEnqueue_one :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (chunk : α) (a :
    Whatwg.Streams.Readable.Algorithms),
    Whatwg.Streams.Readable.canCloseOrEnqueue s = true → s.readRequests = [] →
    s.algorithms = some a → a.size = .one →
      Whatwg.Streams.Readable.beginEnqueue s chunk = Whatwg.Streams.Readable.finishEnqueue
        { s with
          nextEnqueue := s.nextEnqueue + 1 } s.nextEnqueue chunk (.value
            Whatwg.Streams.Readable.sizes.one))

#check (@Whatwg.Streams.Readable.beginEnqueue_foreign :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (chunk : α) (a :
    Whatwg.Streams.Readable.Algorithms)
    (name : Nat), Whatwg.Streams.Readable.canCloseOrEnqueue s = true → s.readRequests = [] →
    s.algorithms = some a → a.size = .foreign name →
      Whatwg.Streams.Readable.beginEnqueue s chunk =
        { s with
          nextEnqueue := s.nextEnqueue + 1,
          frames := .size s.nextEnqueue chunk :: s.frames,
          trace := s.trace ++ [.sizeCalled s.nextEnqueue name chunk] })

#check (@Whatwg.Streams.Readable.beginEnqueue_missing :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (chunk : α),
    Whatwg.Streams.Readable.canCloseOrEnqueue s = true → s.readRequests = [] → s.algorithms = none →
      Whatwg.Streams.Readable.beginEnqueue s chunk = s)

#check (@Whatwg.Streams.Readable.finishEnqueue_value :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (call : Nat) (chunk : α)
    (size : Whatwg.Streams.Readable.Size) (q : Whatwg.Streams.Data.Queue α
      Whatwg.Streams.Readable.Size),
    Whatwg.Streams.Data.enqueueValueWithSize Whatwg.Streams.Readable.sizes s.queue chunk size = .ok
      q →
      Whatwg.Streams.Readable.finishEnqueue s call chunk (.value size) =
        Whatwg.Streams.Readable.callPullIfNeededWith { s with queue := q } (.returnEnqueue call))

#check (@Whatwg.Streams.Readable.finishEnqueue_invalid :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (call : Nat) (chunk : α)
    (size : Whatwg.Streams.Readable.Size),
    Whatwg.Streams.Data.enqueueValueWithSize Whatwg.Streams.Readable.sizes s.queue chunk size =
      .error .rangeError →
      Whatwg.Streams.Readable.finishEnqueue s call chunk (.value size) =
        let e : Whatwg.Streams.Boundary.Exception ε :=
          Whatwg.Streams.Boundary.Exception.ofRangeError s.nextError .rangeError
        let t := Whatwg.Streams.Readable.error { s with nextError := s.nextError + 1 } e
        { t with
          trace := t.trace ++ [.enqueueReturned call (.error e)] })

#check (@Whatwg.Streams.Readable.finishEnqueue_thrown :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (call : Nat) (chunk : α)
    (e : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Readable.finishEnqueue s call chunk (.thrown e) =
      let t := Whatwg.Streams.Readable.error s e
      { t with
        trace := t.trace ++ [.enqueueReturned call (.error e)] })

#check (@Whatwg.Streams.Readable.resumeSize_empty :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε)
    (answer : Whatwg.Streams.Data.SizeAnswer Whatwg.Streams.Readable.Size
      (Whatwg.Streams.Boundary.Exception ε)),
    s.frames = [] → Whatwg.Streams.Readable.resumeSize s answer = none)


/-! Observation masks and the relational external-decision face. -/

#check (@Whatwg.Streams.Readable.settlementTrace_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.settlementTrace s = s.trace.filterMap (fun event ↦
      match event with
      | .settled settlement => some settlement
      | _ => none))

#check (@Whatwg.Streams.Readable.chunksOfSettlements_eq :
  ∀ {α ε : Type} (events : List (Whatwg.Streams.Readable.Settlement α ε)),
    Whatwg.Streams.Readable.chunksOfSettlements events = events.filterMap (fun event ↦
      match event with
      | .read _ (.ok (.chunk chunk)) => some chunk
      | _ => none))

#check (@Whatwg.Streams.Readable.observeM1_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.observeM1 s = (Whatwg.Streams.Readable.chunksOfSettlements
      (Whatwg.Streams.Readable.settlementTrace s), s.status))

#check (@Whatwg.Streams.Readable.chunksOfSettlements_append :
  ∀ {α ε : Type} (left right : List (Whatwg.Streams.Readable.Settlement α ε)),
    Whatwg.Streams.Readable.chunksOfSettlements (left ++ right) =
      Whatwg.Streams.Readable.chunksOfSettlements left ++
        Whatwg.Streams.Readable.chunksOfSettlements right)

#check (@Whatwg.Streams.Readable.Decision.read :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.Decision α ε)

#check (@Whatwg.Streams.Readable.Decision.enqueue :
  ∀ {α ε : Type}, α → Whatwg.Streams.Readable.Decision α ε)

#check (@Whatwg.Streams.Readable.Decision.close :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.Decision α ε)

#check (@Whatwg.Streams.Readable.Decision.error :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Readable.Decision α ε)

#check (@Whatwg.Streams.Readable.Decision.size :
  ∀ {α ε : Type}, Whatwg.Streams.Data.SizeAnswer Whatwg.Streams.Readable.Size
    (Whatwg.Streams.Boundary.Exception ε) → Whatwg.Streams.Readable.Decision α ε)

#check (@Whatwg.Streams.Readable.Decision.pull :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.PullAnswer ε → Whatwg.Streams.Readable.Decision α ε)

#check (@Whatwg.Streams.Readable.step :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.Decision α ε → Option
    (Whatwg.Streams.Readable.State α ε))

#check (@Whatwg.Streams.Readable.Step :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.Decision α ε →
    Whatwg.Streams.Readable.State α ε → Prop)

#check (@Whatwg.Streams.Readable.Steps :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → List (Whatwg.Streams.Readable.Decision α ε) →
    Whatwg.Streams.Readable.State α ε → Prop)

#check (@Whatwg.Streams.Readable.step_read :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.step s .read = some (Whatwg.Streams.Readable.read s))

#check (@Whatwg.Streams.Readable.step_enqueue :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (chunk : α),
    Whatwg.Streams.Readable.step s (.enqueue chunk) = some (Whatwg.Streams.Readable.beginEnqueue s
      chunk))

#check (@Whatwg.Streams.Readable.step_close :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.step s .close = some (Whatwg.Streams.Readable.close s))

#check (@Whatwg.Streams.Readable.step_error :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Readable.step s (.error e) = some (Whatwg.Streams.Readable.error s e))

#check (@Whatwg.Streams.Readable.step_size :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (a : Whatwg.Streams.Data.SizeAnswer
    Whatwg.Streams.Readable.Size (Whatwg.Streams.Boundary.Exception ε)),
    Whatwg.Streams.Readable.step s (.size a) = Whatwg.Streams.Readable.resumeSize s a)

#check (@Whatwg.Streams.Readable.step_pull :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (a : Whatwg.Streams.Readable.PullAnswer ε),
    Whatwg.Streams.Readable.step s (.pull a) = Whatwg.Streams.Readable.acceptPullAnswer s a)

#check (@Whatwg.Streams.Readable.step_iff :
  ∀ {α ε : Type} (s t : Whatwg.Streams.Readable.State α ε) (d : Whatwg.Streams.Readable.Decision α
    ε),
    Whatwg.Streams.Readable.Step s d t ↔ Whatwg.Streams.Readable.step s d = some t)

#check (@Whatwg.Streams.Readable.steps_nil_iff :
  ∀ {α ε : Type} (s t : Whatwg.Streams.Readable.State α ε), Whatwg.Streams.Readable.Steps s [] t ↔
    s = t)

#check (@Whatwg.Streams.Readable.steps_cons_iff :
  ∀ {α ε : Type} (s t : Whatwg.Streams.Readable.State α ε) (d : Whatwg.Streams.Readable.Decision α
    ε)
    (ds : List (Whatwg.Streams.Readable.Decision α ε)), Whatwg.Streams.Readable.Steps s (d :: ds) t
      ↔
      ∃ mid, Whatwg.Streams.Readable.Step s d mid ∧ Whatwg.Streams.Readable.Steps mid ds t)

#check (@Whatwg.Streams.Readable.steps_append_iff :
  ∀ {α ε : Type} (s t : Whatwg.Streams.Readable.State α ε)
    (left right : List (Whatwg.Streams.Readable.Decision α ε)), Whatwg.Streams.Readable.Steps s
      (left ++ right) t ↔
      ∃ mid, Whatwg.Streams.Readable.Steps s left mid ∧ Whatwg.Streams.Readable.Steps mid right t)


/-! Quantified production regressions for the pinned reentrant algorithms. M1 and the
  settlement-order component of M2 named. -/

#check (@Whatwg.Streams.Readable.reentrant_enqueue_lifo :
  ∀ {α ε : Type} (a b : α),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t u : Whatwg.Streams.Readable.State α ε,
      Whatwg.Streams.Readable.resumeSize (Whatwg.Streams.Readable.beginEnqueue
        (Whatwg.Streams.Readable.beginEnqueue s a) b)
        (.value Whatwg.Streams.Readable.sizes.one) = some t ∧
      Whatwg.Streams.Readable.resumeSize t (.value Whatwg.Streams.Readable.sizes.one) = some u ∧
      u.queue.entries.map Whatwg.Streams.Data.QueueEntry.value = [b, a] ∧ u.frames = [])

#check (@Whatwg.Streams.Readable.reentrant_close_keeps_chunk :
  ∀ {α ε : Type} (a : α),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : Whatwg.Streams.Readable.State α ε, Whatwg.Streams.Readable.resumeSize
      (Whatwg.Streams.Readable.close (Whatwg.Streams.Readable.beginEnqueue s a))
      (.value Whatwg.Streams.Readable.sizes.one) = some t ∧
      t.status = .closed ∧ t.queue.entries.map Whatwg.Streams.Data.QueueEntry.value = [a] ∧
      Whatwg.Streams.Readable.observeM1 (Whatwg.Streams.Readable.read t) = ([], .closed))

#check (@Whatwg.Streams.Readable.reentrant_read_does_not_recheck :
  ∀ {α ε : Type} (a b : α),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t u : Whatwg.Streams.Readable.State α ε,
      Whatwg.Streams.Readable.returnPull (Whatwg.Streams.Readable.read
        (Whatwg.Streams.Readable.beginEnqueue s a)) .pending = some t ∧
      Whatwg.Streams.Readable.resumeSize t (.value Whatwg.Streams.Readable.sizes.one) = some u ∧
      u.readRequests = [0] ∧ u.queue.entries.map Whatwg.Streams.Data.QueueEntry.value = [a] ∧
      Whatwg.Streams.Readable.observeM1 (Whatwg.Streams.Readable.read
        (Whatwg.Streams.Readable.beginEnqueue u b)) = ([b, a], .readable))

#check (@Whatwg.Streams.Readable.reentrant_error_keeps_chunk :
  ∀ {α ε : Type} (a : α) (e : ε),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : Whatwg.Streams.Readable.State α ε, Whatwg.Streams.Readable.resumeSize
      (Whatwg.Streams.Readable.error (Whatwg.Streams.Readable.beginEnqueue s a) (.foreign e))
      (.value Whatwg.Streams.Readable.sizes.one) = some t ∧
      t.status = .errored (.foreign e) ∧ t.queue.entries.map Whatwg.Streams.Data.QueueEntry.value =
        [a] ∧
      Whatwg.Streams.Readable.observeM1 (Whatwg.Streams.Readable.read t) = ([], .errored (.foreign
        e)))

#check (@Whatwg.Streams.Readable.reentrant_error_then_throw :
  ∀ {α ε : Type} (a : α) (stored thrown : ε),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : Whatwg.Streams.Readable.State α ε, Whatwg.Streams.Readable.resumeSize
      (Whatwg.Streams.Readable.error (Whatwg.Streams.Readable.beginEnqueue s a) (.foreign stored))
      (.thrown (.foreign thrown)) = some t ∧
      t.status = .errored (.foreign stored) ∧
      t.trace.getLast? = some (.enqueueReturned 0 (.error (.foreign thrown))))

#check (@Whatwg.Streams.Readable.reentrant_error_then_invalid :
  ∀ {α ε : Type} (a : α) (stored : ε),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : Whatwg.Streams.Readable.State α ε,
      Whatwg.Streams.Readable.resumeSize (Whatwg.Streams.Readable.error
        (Whatwg.Streams.Readable.beginEnqueue s a) (.foreign stored))
        (.value .posInfinity) = some t ∧
      t.status = .errored (.foreign stored) ∧ t.nextError = 1 ∧
      t.trace.getLast? = some (.enqueueReturned 0 (.error (.rangeError 0))))

#check (@Whatwg.Streams.Readable.fifo_close_m1_m2 :
  ∀ {α ε : Type} (a b : α),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 11, cancel := 13 } (.finite 0)
    let t := Whatwg.Streams.Readable.read (Whatwg.Streams.Readable.read
      (Whatwg.Streams.Readable.close
      (Whatwg.Streams.Readable.beginEnqueue (Whatwg.Streams.Readable.beginEnqueue s a) b)))
    Whatwg.Streams.Readable.observeM1 t = ([a, b], .closed) ∧
      Whatwg.Streams.Readable.settlementTrace t = [.read 0 (.ok (.chunk a)), .closed (.ok ()),
        .read 1 (.ok (.chunk b))])

#check (@Whatwg.Streams.Readable.pending_read_skips_size :
  ∀ {α ε : Type} (a : α),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : Whatwg.Streams.Readable.State α ε, Whatwg.Streams.Readable.returnPull
      (Whatwg.Streams.Readable.read s) .pending = some t ∧
      let u := Whatwg.Streams.Readable.beginEnqueue t a
      u.frames = [] ∧ u.queue.entries = [] ∧
        Whatwg.Streams.Readable.settlementTrace u = [.read 0 (.ok (.chunk a))] ∧
        u.trace = [.pullCalled 11, .settled (.read 0 (.ok (.chunk a))),
          .enqueueReturned 0 (.ok ())])

#check (@Whatwg.Streams.Boundary.Exception.typeError_eq_iff :
  ∀ {ε : Type} (left right : Nat),
    (Whatwg.Streams.Boundary.Exception.typeError left : Whatwg.Streams.Boundary.Exception ε) =
      .typeError right ↔ left = right)

#check (@Whatwg.Streams.Readable.PullContinuation :
  Type → Type)

#check (@Whatwg.Streams.Readable.PullContinuation.done :
  ∀ {α : Type}, Whatwg.Streams.Readable.PullContinuation α)

#check (@Whatwg.Streams.Readable.PullContinuation.settleRead :
  ∀ {α : Type}, Nat → α → Whatwg.Streams.Readable.PullContinuation α)

#check (@Whatwg.Streams.Readable.PullContinuation.returnEnqueue :
  ∀ {α : Type}, Nat → Whatwg.Streams.Readable.PullContinuation α)

#check (@Whatwg.Streams.Readable.Frame.size :
  ∀ {α : Type}, Nat → α → Whatwg.Streams.Readable.Frame α)

#check (@Whatwg.Streams.Readable.Frame.pull :
  ∀ {α : Type}, Whatwg.Streams.Readable.PullContinuation α → Whatwg.Streams.Readable.Frame α)

#check (@Whatwg.Streams.Readable.PullReturn :
  Type → Type)

#check (@Whatwg.Streams.Readable.PullReturn.pending :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PullReturn ε)

#check (@Whatwg.Streams.Readable.PullReturn.settled :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PullAnswer ε → Whatwg.Streams.Readable.PullReturn ε)

#check (@Whatwg.Streams.Readable.State.nextError :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Nat)

#check (@Whatwg.Streams.Readable.continuePull :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.PullContinuation α →
    Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.callPullIfNeededWith :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.PullContinuation α →
    Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.returnPull :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.PullReturn ε → Option
    (Whatwg.Streams.Readable.State α ε))

#check (@Whatwg.Streams.Readable.streamClose :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.continuePull_done :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε), Whatwg.Streams.Readable.continuePull s
    .done = s)

#check (@Whatwg.Streams.Readable.continuePull_read :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (id : Nat) (chunk : α),
    Whatwg.Streams.Readable.continuePull s (.settleRead id chunk) =
      { s with
        readPromises := s.readPromises.map (fun p ↦
          if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p),
        trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] })

#check (@Whatwg.Streams.Readable.continuePull_enqueue :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (call : Nat),
    Whatwg.Streams.Readable.continuePull s (.returnEnqueue call) =
      { s with
        trace := s.trace ++ [.enqueueReturned call (.ok ())] })

#check (@Whatwg.Streams.Readable.callPullIfNeeded_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.callPullIfNeeded s = Whatwg.Streams.Readable.callPullIfNeededWith s
      .done)

#check (@Whatwg.Streams.Readable.callPullIfNeededWith_idle :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (k :
    Whatwg.Streams.Readable.PullContinuation α),
    Whatwg.Streams.Readable.shouldCallPull s = false →
      Whatwg.Streams.Readable.callPullIfNeededWith s k = Whatwg.Streams.Readable.continuePull s k)

#check (@Whatwg.Streams.Readable.callPullIfNeededWith_busy :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (k :
    Whatwg.Streams.Readable.PullContinuation α),
    Whatwg.Streams.Readable.shouldCallPull s = true → s.pulling = true →
      Whatwg.Streams.Readable.callPullIfNeededWith s k = Whatwg.Streams.Readable.continuePull { s
        with pullAgain := true } k)

#check (@Whatwg.Streams.Readable.callPullIfNeededWith_start :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (k :
    Whatwg.Streams.Readable.PullContinuation α)
    (a : Whatwg.Streams.Readable.Algorithms), Whatwg.Streams.Readable.shouldCallPull s = true →
      s.pulling = false →
    s.algorithms = some a → Whatwg.Streams.Readable.callPullIfNeededWith s k =
      { s with
        pulling := true, pullAwaiting := false, frames := .pull k :: s.frames,
        trace := s.trace ++ [.pullCalled a.pull] })

#check (@Whatwg.Streams.Readable.callPullIfNeededWith_missing :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (k :
    Whatwg.Streams.Readable.PullContinuation α),
    Whatwg.Streams.Readable.shouldCallPull s = true → s.pulling = false → s.algorithms = none →
      Whatwg.Streams.Readable.callPullIfNeededWith s k = Whatwg.Streams.Readable.continuePull s k)

#check (@Whatwg.Streams.Readable.returnPull_empty :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (result :
    Whatwg.Streams.Readable.PullReturn ε),
    s.frames = [] → Whatwg.Streams.Readable.returnPull s result = none)

#check (@Whatwg.Streams.Readable.returnPull_size :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (call : Nat) (chunk : α)
    (rest : List (Whatwg.Streams.Readable.Frame α)) (result : Whatwg.Streams.Readable.PullReturn ε),
    s.frames = .size call chunk :: rest → Whatwg.Streams.Readable.returnPull s result = none)

#check (@Whatwg.Streams.Readable.returnPull_pending :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (k :
    Whatwg.Streams.Readable.PullContinuation α)
    (rest : List (Whatwg.Streams.Readable.Frame α)), s.frames = .pull k :: rest →
      Whatwg.Streams.Readable.returnPull s .pending =
        some (Whatwg.Streams.Readable.continuePull { s with frames := rest, pullAwaiting := true }
          k))

#check (@Whatwg.Streams.Readable.returnPull_settled :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (k :
    Whatwg.Streams.Readable.PullContinuation α)
    (rest : List (Whatwg.Streams.Readable.Frame α)) (answer : Whatwg.Streams.Readable.PullAnswer ε),
    s.frames = .pull k :: rest → Whatwg.Streams.Readable.returnPull s (.settled answer) =
      some (Whatwg.Streams.Readable.continuePull
        { s with
          frames := rest, pullAwaiting := false, jobs := s.jobs ++ [answer] } k))

#check (@Whatwg.Streams.Readable.streamClose_readable :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε), s.status = .readable →
    Whatwg.Streams.Readable.streamClose s =
      { s with
        status := .closed, readRequests := [], closedPromise := .fulfilled (),
        readPromises := s.readPromises.map (fun p ↦
          if p.1 ∈ s.readRequests then (p.1, .fulfilled .done) else p),
        trace := s.trace ++ [.settled (.closed (.ok ()))] ++
          s.readRequests.map (fun id ↦ .settled (.read id (.ok .done))) })

#check (@Whatwg.Streams.Readable.streamClose_terminal :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    s.status ≠ .readable → Whatwg.Streams.Readable.streamClose s = s)

#check (@Whatwg.Streams.Readable.read_queued_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (chunk : α)
    (q : Whatwg.Streams.Data.Queue α Whatwg.Streams.Readable.Size), s.status = .readable →
    Whatwg.Streams.Data.dequeueValue Whatwg.Streams.Readable.sizes s.queue = some (chunk, q) →
      Whatwg.Streams.Readable.read s =
        let t : Whatwg.Streams.Readable.State α ε :=
          { s with
            queue := q, nextRead := s.nextRead + 1,
            readPromises := s.readPromises ++ [(s.nextRead, .pending)] }
        if s.closeRequested = true ∧ q.entries = [] then
          Whatwg.Streams.Readable.continuePull (Whatwg.Streams.Readable.streamClose { t with
            algorithms := none })
            (.settleRead s.nextRead chunk)
        else Whatwg.Streams.Readable.callPullIfNeededWith t (.settleRead s.nextRead chunk))

#check (@Whatwg.Streams.Readable.finishEnqueue_thrown_nextError :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (call : Nat) (chunk : α)
    (e : Whatwg.Streams.Boundary.Exception ε),
    (Whatwg.Streams.Readable.finishEnqueue s call chunk (.thrown e)).nextError = s.nextError)

#check (@Whatwg.Streams.Readable.resumeSize_size :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (call : Nat) (chunk : α)
    (rest : List (Whatwg.Streams.Readable.Frame α))
    (answer : Whatwg.Streams.Data.SizeAnswer Whatwg.Streams.Readable.Size
      (Whatwg.Streams.Boundary.Exception ε)),
    s.frames = .size call chunk :: rest → Whatwg.Streams.Readable.resumeSize s answer =
      some (Whatwg.Streams.Readable.finishEnqueue { s with frames := rest } call chunk answer))

#check (@Whatwg.Streams.Readable.resumeSize_pull :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (k :
    Whatwg.Streams.Readable.PullContinuation α)
    (rest : List (Whatwg.Streams.Readable.Frame α))
    (answer : Whatwg.Streams.Data.SizeAnswer Whatwg.Streams.Readable.Size
      (Whatwg.Streams.Boundary.Exception ε)),
    s.frames = .pull k :: rest → Whatwg.Streams.Readable.resumeSize s answer = none)

#check (@Whatwg.Streams.Readable.pull_reentrant_error_before_chunk :
  ∀ {α ε : Type} (a : α) (e : ε),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 11, cancel := 13 } Whatwg.Streams.Readable.sizes.one
    let waiting := Whatwg.Streams.Readable.read (Whatwg.Streams.Readable.beginEnqueue s a)
    ∃ t : Whatwg.Streams.Readable.State α ε,
      Whatwg.Streams.Readable.returnPull (Whatwg.Streams.Readable.error waiting (.foreign e))
        .pending = some t ∧
      t.status = .errored (.foreign e) ∧
      Whatwg.Streams.Readable.settlementTrace t = [.closed (.error (.foreign e)), .read 0 (.ok
        (.chunk a))])

#check (@Whatwg.Streams.Readable.pull_reentrant_enqueue_changes_queue :
  ∀ {α ε : Type} (a b : α),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 11, cancel := 13 } Whatwg.Streams.Readable.sizes.one
    let waiting := Whatwg.Streams.Readable.read (Whatwg.Streams.Readable.beginEnqueue s a)
    ∃ t : Whatwg.Streams.Readable.State α ε,
      Whatwg.Streams.Readable.returnPull (Whatwg.Streams.Readable.beginEnqueue waiting b) .pending
        = some t ∧
      t.queue.entries.map Whatwg.Streams.Data.QueueEntry.value = [b] ∧
      Whatwg.Streams.Readable.observeM1 t = ([a], .readable))

#check (@Whatwg.Streams.Readable.pull_reentrant_read_overtakes :
  ∀ {α ε : Type} (a b : α),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 11, cancel := 13 } Whatwg.Streams.Readable.sizes.one
    let waiting := Whatwg.Streams.Readable.read (Whatwg.Streams.Readable.beginEnqueue s a)
    ∃ t : Whatwg.Streams.Readable.State α ε,
      Whatwg.Streams.Readable.returnPull (Whatwg.Streams.Readable.beginEnqueue
        (Whatwg.Streams.Readable.read waiting) b) .pending = some t ∧
      Whatwg.Streams.Readable.settlementTrace t = [.read 1 (.ok (.chunk b)), .read 0 (.ok (.chunk
        a))])

#check (@Whatwg.Streams.Readable.nested_invalid_sizes_fresh_errors :
  ∀ {α ε : Type} (a b : α),
    let s := Whatwg.Streams.Readable.initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t u : Whatwg.Streams.Readable.State α ε,
      Whatwg.Streams.Readable.resumeSize (Whatwg.Streams.Readable.beginEnqueue
        (Whatwg.Streams.Readable.beginEnqueue s a) b)
        (.value .posInfinity) = some t ∧
      Whatwg.Streams.Readable.resumeSize t (.value .posInfinity) = some u ∧
      u.status = .errored (.rangeError 0) ∧ u.nextError = 2 ∧
      u.trace.getLast? = some (.enqueueReturned 0 (.error (.rangeError 1))))

#check (@Whatwg.Streams.Readable.Event.desiredSizeRead :
  ∀ {α ε : Type}, Option Whatwg.Streams.Readable.Size → Whatwg.Streams.Readable.Event α ε)

#check (@Whatwg.Streams.Readable.VisibleEvent :
  Type → Type → Type)

#check (@Whatwg.Streams.Readable.VisibleEvent.settlement :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.Settlement α ε → Whatwg.Streams.Readable.VisibleEvent α ε)

#check (@Whatwg.Streams.Readable.VisibleEvent.desiredSizeRead :
  ∀ {α ε : Type}, Option Whatwg.Streams.Readable.Size → Whatwg.Streams.Readable.VisibleEvent α ε)

#check (@Whatwg.Streams.Readable.VisibleEvent.enqueueReturned :
  ∀ {α ε : Type}, Nat → Except (Whatwg.Streams.Boundary.Exception ε) Unit →
    Whatwg.Streams.Readable.VisibleEvent α ε)

#check (@Whatwg.Streams.Readable.M2Observation :
  Type → Type → Type)

#check (@Whatwg.Streams.Readable.M2Observation.mk :
  ∀ {α ε : Type}, (List α × Whatwg.Streams.Readable.Status ε) →
    List (Whatwg.Streams.Readable.VisibleEvent α ε) → Whatwg.Streams.Readable.M2Observation α ε)

#check (@Whatwg.Streams.Readable.M2Observation.m1 :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.M2Observation α ε → List α ×
    Whatwg.Streams.Readable.Status ε)

#check (@Whatwg.Streams.Readable.M2Observation.visible :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.M2Observation α ε →
    List (Whatwg.Streams.Readable.VisibleEvent α ε))

#check (@Whatwg.Streams.Readable.observeM2 :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.M2Observation α ε)

#check (@Whatwg.Streams.Readable.queryDesiredSize :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.State α ε → Whatwg.Streams.Readable.State α ε)

#check (@Whatwg.Streams.Readable.queryDesiredSize_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.queryDesiredSize s =
      { s with
        trace := s.trace ++ [.desiredSizeRead (Whatwg.Streams.Readable.desiredSize s)] })

#check (@Whatwg.Streams.Readable.observeM2_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε), Whatwg.Streams.Readable.observeM2 s =
    { m1 := Whatwg.Streams.Readable.observeM1 s,
      visible := s.trace.filterMap (fun event ↦
        match event with
        | .settled settlement => some (.settlement settlement)
        | .desiredSizeRead size => some (.desiredSizeRead size)
        | .enqueueReturned call result => some (.enqueueReturned call result)
        | _ => none) })

#check (@Whatwg.Streams.Readable.observeM2_toM1 :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    (Whatwg.Streams.Readable.observeM2 s).m1 = Whatwg.Streams.Readable.observeM1 s)

#check (@Whatwg.Streams.Readable.queryDesiredSize_m2 :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    (Whatwg.Streams.Readable.observeM2 (Whatwg.Streams.Readable.queryDesiredSize s)).visible =
      (Whatwg.Streams.Readable.observeM2 s).visible ++ [.desiredSizeRead
        (Whatwg.Streams.Readable.desiredSize s)])

#check (@Whatwg.Streams.Readable.Decision.pullReturn :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.PullReturn ε → Whatwg.Streams.Readable.Decision α ε)

#check (@Whatwg.Streams.Readable.Decision.desiredSize :
  ∀ {α ε : Type}, Whatwg.Streams.Readable.Decision α ε)

#check (@Whatwg.Streams.Readable.step_pullReturn :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε) (result :
    Whatwg.Streams.Readable.PullReturn ε),
    Whatwg.Streams.Readable.step s (.pullReturn result) = Whatwg.Streams.Readable.returnPull s
      result)

#check (@Whatwg.Streams.Readable.step_desiredSize :
  ∀ {α ε : Type} (s : Whatwg.Streams.Readable.State α ε),
    Whatwg.Streams.Readable.step s .desiredSize = some (Whatwg.Streams.Readable.queryDesiredSize s))
