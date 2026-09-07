import Whatwg.Streams

/-!
Frozen P5a composed-lifecycle addendum, 2026-09-05. Graph: WRITABLE-PG-DEFAULT.
The exact initial snapshots, explicit decisions, deterministic ticks and local ordered views
are the scope. Chunks and error reasons are quantified; the tape shapes remain fixed.
This addendum changes no declaration or equation in the 162/108 base packet.
-/

set_option autoImplicit false

/-! Quantified composed lifecycle obligations under the named local ordered view. -/

-- WRITE; BACKPRESSURE; CLOSE; PROCESSWRITE; PROCESSCLOSE; CLOSEOK
#check (@Whatwg.Streams.Writable.lifecycle_write_close :
  ∀ {α ε : Type} (chunk : α),
    let start := Whatwg.Streams.Writable.initial (α := α) (ε := ε) Whatwg.Streams.Writable.sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    ∃ blocked done : Whatwg.Streams.Writable.State α ε,
      Whatwg.Streams.Writable.Reaches start
        [some .queryReady, some (.write chunk), none, none, none, none,
          some (.returnSink .pending), none, some .queryReady, some .queryDesiredSize] blocked ∧
      blocked.backpressure = true ∧ blocked.readyPromise = 3 ∧
      Whatwg.Streams.Writable.lookupPromise blocked 0 = some (.fulfilled ()) ∧
      Whatwg.Streams.Writable.lookupPromise blocked 3 = some .pending ∧
      Whatwg.Streams.Writable.desiredSize blocked = some Whatwg.Streams.Writable.sizes.zero ∧
      Whatwg.Streams.Writable.Reaches blocked
        [some .close, none, none, none, some .queryReady, some .queryDesiredSize,
          some (.answer .write 2 .fulfilled), none, none, none,
          some (.returnSink (.settled .fulfilled)), none, none] done ∧
      done.status = .closed ∧ done.backpressure = true ∧ done.readyPromise = 3 ∧
      Whatwg.Streams.Writable.lookupPromise done 0 = some (.fulfilled ()) ∧
      Whatwg.Streams.Writable.lookupPromise done 1 = some (.fulfilled ()) ∧
      Whatwg.Streams.Writable.lookupPromise done 3 = some (.fulfilled ()) ∧
      Whatwg.Streams.Writable.lookupPromise done 4 = some (.fulfilled ()) ∧
      Whatwg.Streams.Writable.observeOrdered done =
        ⟨⟨[chunk], .closed⟩,
          [.readyRead 0 0, .returned 1 2, .readyRead 2 3,
            .desiredSizeRead 3 (some Whatwg.Streams.Writable.sizes.zero), .settled 3 (.ok ()),
            .returned 4 4, .readyRead 5 3, .desiredSizeRead 6 (some Whatwg.Streams.Writable.sizes.zero),
            .settled 2 (.ok ()), .settled 4 (.ok ()), .settled 1 (.ok ())]⟩)

-- WRITE; ABORT; STARTERROR; WRITEFAIL; FINISHERROR; ABORTSTEPS; REJECTCLOSED
#check (@Whatwg.Streams.Writable.lifecycle_abort_rejection :
  ∀ {α ε : Type} (first second : α) (abortReason writeReason : Whatwg.Streams.Boundary.Exception ε),
    writeReason ≠ abortReason →
    let start := Whatwg.Streams.Writable.initial (α := α) (ε := ε) Whatwg.Streams.Writable.sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    ∃ blocked done : Whatwg.Streams.Writable.State α ε,
      Whatwg.Streams.Writable.Reaches start
        [some (.write first), none, none, none, none, some (.returnSink .pending), none,
          some (.write second), none, none, none, none, none,
          some (.abort abortReason), none, some .returnSignal, none, none, none] blocked ∧
      blocked.status = .erroring abortReason ∧
      blocked.inFlightWrite = some (2, .awaiting) ∧ blocked.writeRequests = [4] ∧
      blocked.pendingAbort = some (.requested 5 abortReason) ∧
      Whatwg.Streams.Writable.lookupPromise blocked 0 = some (.fulfilled ()) ∧
      Whatwg.Streams.Writable.lookupPromise blocked 3 = some (.rejected abortReason) ∧
      Whatwg.Streams.Writable.Reaches blocked
        [some (.answer .write 2 (.rejected writeReason)), none, none, none, none,
          some (.returnSink (.settled .fulfilled)), none, none, none] done ∧
      done.status = .errored abortReason ∧ done.pendingAbort = none ∧
      done.inFlightWrite = none ∧ done.abortInFlight = none ∧ done.writeRequests = [] ∧
      done.queue = Whatwg.Streams.Data.Queue.empty Whatwg.Streams.Writable.sizes ∧
      Whatwg.Streams.Writable.lookupPromise done 0 = some (.fulfilled ()) ∧
      Whatwg.Streams.Writable.lookupPromise done 1 = some (.rejected abortReason) ∧
      Whatwg.Streams.Writable.lookupPromise done 2 = some (.rejected writeReason) ∧
      Whatwg.Streams.Writable.lookupPromise done 4 = some (.rejected abortReason) ∧
      Whatwg.Streams.Writable.lookupPromise done 5 = some (.fulfilled ()) ∧
      Whatwg.Streams.Writable.observeOrdered done =
        ⟨⟨[first], .errored abortReason⟩,
          [.returned 0 2, .returned 1 4, .settled 3 (.error abortReason),
            .returned 2 5, .settled 2 (.error writeReason), .settled 4 (.error abortReason),
            .settled 5 (.ok ()), .settled 1 (.error abortReason)]⟩)
