import Whatwg.Streams

/-! P7a breaker composed obligations; freeze state and receipts: owning contract.
Chunks and reasons are quantified, while each explicit tape shape is finite.
The endpoint is the named readyToFinalize frontier, not a settled pipe result.
-/

set_option autoImplicit false
open Whatwg.Streams

#check (@Piping.lifecycle_two_writes_abort_rejection :
  ∀ {α ε : Type} (first second : α) (sourceReason actionReason : Boundary.Exception ε),
    actionReason ≠ sourceReason →
    let r0 := Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 10, cancel := 11 } Readable.sizes.zero
    let w0 := Writable.initial (α := α) (ε := ε) Writable.sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    ∃ r : Readable.State α ε,
      Readable.Steps r0 [.enqueue first, .read, .enqueue second, .read] r ∧
      Piping.deliveredReads r = [(0, first), (1, second)] ∧
      let start := Piping.initial r w0 false
      Piping.Admitted start ∧
      ∃ writing blocked secondBlocked done : Piping.State α ε,
        Piping.Reaches start
          (List.replicate 5 none ++
            [some (.writable (.returnSink .pending)), none, none]) writing ∧
        writing.phase = .running ∧
        Writable.lookupPromise writing.destination 2 = some .pending ∧
        Piping.Reaches writing
          (some (.sourceError sourceReason) :: List.replicate 9 none) blocked ∧
        blocked.phase = .waitingWrites ∧
        blocked.selection = some ⟨sourceReason, true, false⟩ ∧
        blocked.links = [⟨0, first, .submitted 0 2⟩, ⟨1, second, .submitted 1 4⟩] ∧
        blocked.destination.inFlightWrite = some (2, .awaiting) ∧
        blocked.destination.writeRequests = [4] ∧
        Writable.lookupPromise blocked.destination 2 = some .pending ∧
        Writable.lookupPromise blocked.destination 4 = some .pending ∧
        blocked.abortCall = none ∧ Piping.tick blocked = none ∧
        Piping.Reaches blocked
          [some (.writable (.answer .write 2 .fulfilled)), none, none, none,
            some (.writable (.returnSink .pending))] secondBlocked ∧
        Writable.lookupPromise secondBlocked.destination 2 = some (.fulfilled ()) ∧
        Writable.lookupPromise secondBlocked.destination 4 = some .pending ∧
        secondBlocked.abortCall = none ∧ Piping.tick secondBlocked = none ∧
        Piping.Reaches secondBlocked
          ([some (.writable (.answer .write 4 .fulfilled))] ++ List.replicate 5 none ++
            [some (.writable .returnSignal)] ++ List.replicate 3 none ++
            [some (.writable (.returnSink (.settled (.rejected actionReason))))] ++
            List.replicate 6 none) done ∧
        done.phase = .readyToFinalize actionReason ∧
        done.source.status = .errored sourceReason ∧
        done.destination.status = .errored sourceReason ∧
        done.selection = some ⟨sourceReason, true, false⟩ ∧
        done.abortCall = some 2 ∧ done.abortPromise = some 5 ∧
        Writable.lookupPromise done.destination 2 = some (.fulfilled ()) ∧
        Writable.lookupPromise done.destination 4 = some (.fulfilled ()) ∧
        Writable.lookupPromise done.destination 5 = some (.rejected actionReason) ∧
        Writable.lookupPromise done.destination 1 = some (.rejected sourceReason) ∧
        Writable.sinkInput done.destination = [first, second] ∧
        Piping.ForwardShutdownSpec (Piping.observeShutdown done))

#check (@Piping.lifecycle_write_rejection_retains_source :
  ∀ {α ε : Type} (chunk : α) (sourceReason writeReason : Boundary.Exception ε) (prevent : Bool),
    writeReason ≠ sourceReason →
    let r0 := Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 10, cancel := 11 } Readable.sizes.zero
    let w0 := Writable.initial (α := α) (ε := ε) Writable.sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    ∃ r : Readable.State α ε,
      Readable.Steps r0 [.enqueue chunk, .read] r ∧
      Piping.deliveredReads r = [(0, chunk)] ∧
      let start := Piping.initial r w0 prevent
      Piping.Admitted start ∧
      ∃ writing blocked done : Piping.State α ε,
        Piping.Reaches start
          (List.replicate 5 none ++
            [some (.writable (.returnSink .pending)), none, none]) writing ∧
        Piping.Reaches writing [some (.sourceError sourceReason), none, none] blocked ∧
        blocked.phase = .waitingWrites ∧
        blocked.selection = some ⟨sourceReason, true, prevent⟩ ∧
        blocked.links = [⟨0, chunk, .submitted 0 2⟩] ∧
        Writable.lookupPromise blocked.destination 2 = some .pending ∧
        blocked.abortCall = none ∧ Piping.tick blocked = none ∧
        Piping.Reaches blocked
          ([some (.writable (.answer .write 2 (.rejected writeReason)))] ++
            List.replicate 6 none ++ (if prevent then [none] else List.replicate 5 none)) done ∧
        done.phase = .readyToFinalize sourceReason ∧
        done.source.status = .errored sourceReason ∧
        done.destination.status = .errored writeReason ∧
        done.selection = some ⟨sourceReason, true, prevent⟩ ∧
        done.abortCall = (if prevent then none else some 1) ∧
        done.abortPromise = (if prevent then none else some 4) ∧
        Writable.lookupPromise done.destination 2 = some (.rejected writeReason) ∧
        Writable.lookupPromise done.destination 1 = some (.rejected writeReason) ∧
        (if prevent then True else
          Writable.lookupPromise done.destination 4 = some (.fulfilled ())) ∧
        Writable.sinkInput done.destination = [chunk] ∧
        (∀ name request reason,
          Writable.Event.sinkCalled name (.abort request reason) ∉ done.destination.trace) ∧
        Piping.ForwardShutdownSpec (Piping.observeShutdown done))
