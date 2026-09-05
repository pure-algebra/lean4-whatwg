import Whatwg.Streams

/-! P7a breaker requirements and candidate equations; freeze state: owning contract.
Requirements inspect protocol snapshots and canonical component transitions;
no reference to the candidate control phase occurs in RecordAllowed.
All finite run claims use observeShutdown, not the full DB-04 masks. -/

set_option autoImplicit false
open Whatwg.Streams

#check (@Piping.deliveredReads_eq :
  ∀ {α ε : Type} (s : Readable.State α ε),
  Piping.deliveredReads s = s.trace.filterMap (fun e => match e with
    | .settled (.read id (.ok (.chunk chunk))) => some (id, chunk)
    | _ => none))

#check (@Piping.markWrite_eq :
  ∀ {α : Type} (ls : List (Piping.ReadWriteLink α)) (id : Nat) (stage : Piping.WriteStage),
  Piping.markWrite ls id stage =
    ls.map (fun l => if l.readId = id then { l with write := stage } else l))

#check (@Piping.writesSettled_iff :
  ∀ {α ε : Type} (s : Piping.Snapshot α ε),
  Piping.WritesSettled s ↔ ∀ l ∈ s.links, ∃ call request,
    l.write = .submitted call request ∧
      (Writable.lookupPromise s.destination request = some (.fulfilled ()) ∨
        ∃ reason, Writable.lookupPromise s.destination request = some (.rejected reason)))

#check (@Piping.bodyDecision_iff :
  ∀ {α ε : Type} (d : Writable.Decision α ε),
  Piping.BodyDecision d ↔ (match d with
    | .controllerError _ | .answer _ _ _ | .returnSize _ | .returnSink _ | .returnSignal => True
    | _ => False))

#check (@Piping.readInventory_iff :
  ∀ {α ε : Type} (s : Piping.Snapshot α ε),
  Piping.ReadInventory s ↔
    s.links.map (fun l => (l.readId, l.chunk)) = Piping.deliveredReads s.source ∧
    (s.links.map Piping.ReadWriteLink.readId).Nodup)

#check (@Piping.initialSnapshot_iff :
  ∀ {α ε : Type} (s : Piping.Snapshot α ε),
  Piping.InitialSnapshot s ↔
    Piping.ReadInventory s ∧ (∀ l ∈ s.links, l.write = .unwritten) ∧
    s.selection = none ∧ s.abortCall = none ∧ s.abortPromise = none ∧ s.finalization = none ∧
    s.source.frames = [] ∧ s.source.jobs = [] ∧ s.source.readRequests = [] ∧
    s.source.pulling = false ∧ s.source.pullAwaiting = false ∧
    (s.source.status = .readable ∨ ∃ e, s.source.status = .errored e) ∧
    ∃ hwm algorithms promiseSeed,
      s.destination = Writable.initial hwm algorithms promiseSeed s.source.nextError)

#check (@Piping.recordAllowed_iff :
  ∀ {α ε : Type} (r : Piping.ProtocolRecord α ε),
  Piping.RecordAllowed r ↔
    let b := r.before
    let a := r.after
    b.finalization = none ∧ Piping.ReadInventory b ∧ Piping.ReadInventory a ∧
    a.preventAbort = b.preventAbort ∧ a.source.nextRead = b.source.nextRead ∧
    (match r.event with
    | .selected p =>
        b.selection = none ∧ b.source.status = .errored p.reason ∧
        p.preventAbort = b.preventAbort ∧
        (p.drainRequired = true ↔
          b.destination.status = .writable ∧ b.destination.closeState = .none) ∧
        a = { b with selection := some p }
    | .writeInvoked id chunk call =>
        b.abortCall = none ∧ b.destination.control = [] ∧ call = b.destination.nextCall ∧
        (∃ pre l post, b.links = pre ++ l :: post ∧
          (∀ earlier ∈ pre, earlier.write ≠ .unwritten) ∧
          l.readId = id ∧ l.chunk = chunk ∧ l.write = .unwritten) ∧
        (match b.selection with
          | none => b.source.status = .readable ∧ b.destination.status = .writable ∧
              b.destination.closeState = .none ∧
              ∃ size, Writable.desiredSize b.destination = some size ∧
                Readable.sizePositive size = true
          | some p => p.drainRequired = true) ∧
        Writable.decide b.destination (.write chunk) = some a.destination ∧
        a = { b with
          destination := a.destination,
          links := Piping.markWrite b.links id (.invoking call) }
    | .writeReturned id call request =>
        (∃ l ∈ b.links, l.readId = id ∧ l.write = .invoking call) ∧
        Writable.Event.returned call request ∈ b.destination.trace ∧
        (∃ outcome, Writable.lookupPromise b.destination request = some outcome) ∧
        a = { b with links := Piping.markWrite b.links id (.submitted call request) }
    | .abortInvoked call reason =>
        b.destination.control = [] ∧ b.abortCall = none ∧
        call = b.destination.nextCall ∧
        (∃ p, b.selection = some p ∧ p.preventAbort = false ∧ reason = p.reason ∧
          (p.drainRequired = false ∨ Piping.WritesSettled b)) ∧
        Writable.decide b.destination (.abort reason) = some a.destination ∧
        a = { b with destination := a.destination, abortCall := some call }
    | .abortReturned call request =>
        b.abortCall = some call ∧ b.abortPromise = none ∧
        Writable.Event.returned call request ∈ b.destination.trace ∧
        (∃ outcome, Writable.lookupPromise b.destination request = some outcome) ∧
        a = { b with abortPromise := some request }
    | .readyToFinalize reason =>
        (∃ p, b.selection = some p ∧
          (p.drainRequired = false ∨ Piping.WritesSettled b) ∧
          (if p.preventAbort then
            b.abortCall = none ∧ b.abortPromise = none ∧ reason = p.reason
          else ∃ call request, b.abortCall = some call ∧ b.abortPromise = some request ∧
            ((Writable.lookupPromise b.destination request = some (.fulfilled ()) ∧
                reason = p.reason) ∨
              Writable.lookupPromise b.destination request = some (.rejected reason)))) ∧
        a = { b with finalization := some reason }
    | .writable d =>
        (match d with | none => True | some choice => Piping.BodyDecision choice) ∧
        Writable.Step b.destination d a.destination ∧
        a = { b with destination := a.destination }
    | .sourceError reason =>
        a = { b with source := Readable.error b.source reason }
    | .administrative => a = b))

#check (@Piping.observationChain_nil_iff :
  ∀ {α ε : Type} (a b : Piping.Snapshot α ε),
  Piping.ObservationChain a [] b ↔ a = b)

#check (@Piping.observationChain_cons_iff :
  ∀ {α ε : Type} (a b : Piping.Snapshot α ε)
  (r : Piping.ProtocolRecord α ε) (rs : List (Piping.ProtocolRecord α ε)),
  Piping.ObservationChain a (r :: rs) b ↔
    r.before = a ∧ Piping.ObservationChain r.after rs b)

#check (@Piping.forwardShutdownSpec_iff :
  ∀ {α ε : Type} (o : Piping.ShutdownObservation α ε),
  Piping.ForwardShutdownSpec o ↔ Piping.InitialSnapshot o.initial ∧
    Piping.ObservationChain o.initial o.records o.current ∧
    ∀ r ∈ o.records, Piping.RecordAllowed r)

#check (@Piping.snapshot_eq :
  ∀ {α ε : Type} (s : Piping.State α ε),
  Piping.snapshot s = ⟨s.source, s.destination, s.links, s.preventAbort, s.selection,
    s.abortCall, s.abortPromise,
    match s.phase with | .readyToFinalize reason => some reason | _ => none⟩)

#check (@Piping.initial_eq :
  ∀ {α ε : Type} (r : Readable.State α ε) (w : Writable.State α ε) (prevent : Bool),
  Piping.initial r w prevent =
    let links := (Piping.deliveredReads r).map (fun p => Piping.ReadWriteLink.mk p.1 p.2 .unwritten)
    {
      source := r, destination := w, links := links, preventAbort := prevent,
      selection := none, abortCall := none, abortPromise := none, phase := .running,
      entry := ⟨r, w, links, prevent, none, none, none, none⟩, trace := [] })

#check (@Piping.observeShutdown_eq :
  ∀ {α ε : Type} (s : Piping.State α ε),
  Piping.observeShutdown s = ⟨s.entry, s.trace, Piping.snapshot s⟩)

#check (@Piping.emit_eq :
  ∀ {α ε : Type} (s t : Piping.State α ε) (e : Piping.ProtocolEvent α ε),
  Piping.emit s e t =
    { t with
      entry := s.entry,
      trace := s.trace ++ [⟨Piping.snapshot s, e, Piping.snapshot t⟩] })

#check (@Piping.drainGuard_eq :
  ∀ {α ε : Type} (w : Writable.State α ε),
  Piping.drainGuard w =
    (match w.status with | .writable => !Writable.closeQueuedOrInFlight w | _ => false))

#check (@Piping.drainGuard_true_iff :
  ∀ {α ε : Type} (w : Writable.State α ε),
  Piping.drainGuard w = true ↔ w.status = .writable ∧ w.closeState = .none)

#check (@Piping.nextUnwritten_nil :
  ∀ {α : Type},
  Piping.nextUnwritten ([] : List (Piping.ReadWriteLink α)) = none)

#check (@Piping.nextUnwritten_cons :
  ∀ {α : Type} (l : Piping.ReadWriteLink α) (ls : List (Piping.ReadWriteLink α)),
  Piping.nextUnwritten (l :: ls) =
    (match l.write with | .unwritten => some l | _ => Piping.nextUnwritten ls))

#check (@Piping.allWrittenSettled_eq :
  ∀ {α ε : Type} (w : Writable.State α ε) (ls : List (Piping.ReadWriteLink α)),
  Piping.allWrittenSettled w ls = ls.all (fun l =>
    match l.write with
    | .submitted _ request => match Writable.lookupPromise w request with
        | some (.fulfilled _) | some (.rejected _) => true
        | _ => false
    | _ => false))

#check (@Piping.allWrittenSettled_iff :
  ∀ {α ε : Type} (s : Piping.Snapshot α ε),
  Piping.allWrittenSettled s.destination s.links = true ↔ Piping.WritesSettled s)

#check (@Piping.lookupReturn_eq :
  ∀ {α ε : Type} (w : Writable.State α ε) (call : Nat),
  Piping.lookupReturn w call = w.trace.findSome? (fun e => match e with
    | .returned c request => if c = call then some request else none
    | _ => none))

#check (@Piping.foreignDecision_eq :
  ∀ {α ε : Type} (d : Writable.Decision α ε),
  Piping.foreignDecision d = (match d with
    | .controllerError _ | .answer _ _ _ | .returnSize _ | .returnSink _ | .returnSignal => true
    | _ => false))

#check (@Piping.foreignDecision_iff :
  ∀ {α ε : Type} (d : Writable.Decision α ε),
  Piping.foreignDecision d = true ↔ Piping.BodyDecision d)

#check (@Piping.enterForwardShutdown_eq :
  ∀ {α ε : Type} (s : Piping.State α ε),
  Piping.enterForwardShutdown s =
    (match s.selection, s.source.status with
    | none, .errored reason =>
        let p : Piping.ShutdownPlan ε := ⟨reason, Piping.drainGuard s.destination, s.preventAbort⟩
        Piping.emit s (.selected p) { s with selection := some p, phase := .draining }
    | _, _ => s))

#check (@Piping.enterForwardShutdown_first_wins :
  ∀ {α ε : Type} (s : Piping.State α ε) (p : Piping.ShutdownPlan ε),
  s.selection = some p → Piping.enterForwardShutdown s = s)

#check (@Piping.invokeWrite_eq :
  ∀ {α ε : Type} (s : Piping.State α ε) (l : Piping.ReadWriteLink α),
  Piping.invokeWrite s l = (Writable.decide s.destination (.write l.chunk)).map (fun w =>
    Piping.emit s (.writeInvoked l.readId l.chunk s.destination.nextCall)
      { s with
        destination := w,
        links := Piping.markWrite s.links l.readId (.invoking s.destination.nextCall),
        phase := .returningWrite l.readId s.destination.nextCall }))

#check (@Piping.captureWrite_eq :
  ∀ {α ε : Type} (s : Piping.State α ε) (id call : Nat),
  Piping.captureWrite s id call = (Piping.lookupReturn s.destination call).map (fun request =>
    Piping.emit s (.writeReturned id call request)
      { s with
        links := Piping.markWrite s.links id (.submitted call request),
        phase := match s.selection with | none => .running | some _ => .draining }))

#check (@Piping.invokeAbort_eq :
  ∀ {α ε : Type} (s : Piping.State α ε) (p : Piping.ShutdownPlan ε),
  Piping.invokeAbort s p = (Writable.decide s.destination (.abort p.reason)).map (fun w =>
    Piping.emit s (.abortInvoked s.destination.nextCall p.reason)
      { s with
        destination := w, abortCall := some s.destination.nextCall,
        phase := .returningAbort s.destination.nextCall }))

#check (@Piping.captureAbort_eq :
  ∀ {α ε : Type} (s : Piping.State α ε) (call : Nat),
  Piping.captureAbort s call = (Piping.lookupReturn s.destination call).map (fun request =>
    Piping.emit s (.abortReturned call request)
      { s with abortPromise := some request, phase := .waitingAbort }))

#check (@Piping.requestFinalize_eq :
  ∀ {α ε : Type} (s : Piping.State α ε) (reason : Boundary.Exception ε),
  Piping.requestFinalize s reason =
    Piping.emit s (.readyToFinalize reason) { s with phase := .readyToFinalize reason })

#check (@Piping.stepWritable_eq :
  ∀ {α ε : Type} (s : Piping.State α ε) (d : Option (Writable.Decision α ε)),
  Piping.stepWritable s d =
    (match d with | none => Writable.tick s.destination | some a => Writable.decide s.destination a).map
      (fun w => Piping.emit s (.writable d) { s with destination := w }))

#check (@Piping.externalFrontier_eq :
  ∀ {α ε : Type} (s : Piping.State α ε),
  Piping.externalFrontier s = (match s.phase with
    | .readyToFinalize _ => false
    | _ => if Writable.externalFrontier s.destination then
        match s.destination.control with
        | [] => match s.phase with
            | .running | .waitingWrites | .waitingAbort => true
            | _ => false
        | _ => true
      else false))

#check (@Piping.decide_eq :
  ∀ {α ε : Type} (s : Piping.State α ε) (d : Piping.Decision α ε),
  Piping.decide s d = (if Piping.externalFrontier s then match d with
    | .sourceError e => some (Piping.emit s (.sourceError e)
        { s with source := Readable.error s.source e })
    | .writable a => if Piping.foreignDecision a then Piping.stepWritable s (some a) else none
    else none))

#check (@Piping.tick_eq :
  ∀ {α ε : Type} (s : Piping.State α ε),
  Piping.tick s =
    let action := fun p : Piping.ShutdownPlan ε =>
      if p.preventAbort then some (Piping.requestFinalize s p.reason)
      else Piping.invokeAbort s p
    match s.phase with
    | .readyToFinalize _ => none
    | _ => if s.destination.control ≠ [] then Piping.stepWritable s none
      else match s.phase with
      | .running => match s.source.status with
          | .errored _ => some (Piping.enterForwardShutdown s)
          | .readable =>
              match s.destination.status with
              | .writable =>
                if Writable.closeQueuedOrInFlight s.destination then Piping.stepWritable s none
                else match Writable.desiredSize s.destination, Piping.nextUnwritten s.links with
                  | some size, some l =>
                      if Readable.sizePositive size then Piping.invokeWrite s l
                      else Piping.stepWritable s none
                  | _, _ => Piping.stepWritable s none
              | _ => Piping.stepWritable s none
          | .closed => Piping.stepWritable s none
      | .draining => match s.selection with
          | none => none
          | some p =>
              if p.drainRequired then match Piping.nextUnwritten s.links with
                | some l => Piping.invokeWrite s l
                | none => some (Piping.emit s .administrative { s with phase := .waitingWrites })
              else action p
      | .returningWrite id call => Piping.captureWrite s id call
      | .waitingWrites => match s.selection with
          | none => none
          | some p => if Piping.allWrittenSettled s.destination s.links then action p
              else Piping.stepWritable s none
      | .returningAbort call => Piping.captureAbort s call
      | .waitingAbort => match s.selection, s.abortPromise with
          | some p, some id => match Writable.lookupPromise s.destination id with
              | some (.fulfilled _) => some (Piping.requestFinalize s p.reason)
              | some (.rejected reason) => some (Piping.requestFinalize s reason)
              | _ => Piping.stepWritable s none
          | _, _ => none
      | .readyToFinalize _ => none)

#check (@Piping.step_iff :
  ∀ {α ε : Type} (s t : Piping.State α ε) (d : Option (Piping.Decision α ε)),
  Piping.Step s d t ↔ (match d with | none => Piping.tick s | some a => Piping.decide s a) = some t)

#check (@Piping.reaches_nil_iff :
  ∀ {α ε : Type} (s t : Piping.State α ε),
  Piping.Reaches s [] t ↔ s = t)

#check (@Piping.reaches_cons_iff :
  ∀ {α ε : Type} (s t : Piping.State α ε)
  (d : Option (Piping.Decision α ε)) (ds : List (Option (Piping.Decision α ε))),
  Piping.Reaches s (d :: ds) t ↔ ∃ mid, Piping.Step s d mid ∧ Piping.Reaches mid ds t)

#check (@Piping.reaches_append_iff :
  ∀ {α ε : Type} (s t : Piping.State α ε)
  (left right : List (Option (Piping.Decision α ε))),
  Piping.Reaches s (left ++ right) t ↔
    ∃ mid, Piping.Reaches s left mid ∧ Piping.Reaches mid right t)

#check (@Piping.admitted_iff :
  ∀ {α ε : Type} (s : Piping.State α ε),
  Piping.Admitted s ↔ Piping.InitialSnapshot (Piping.snapshot s) ∧
    s.phase = .running ∧ s.entry = Piping.snapshot s ∧ s.trace = [])

#check (@Piping.forwardShutdown_realizes :
  ∀ {α ε : Type} (s t : Piping.State α ε)
  (tape : List (Option (Piping.Decision α ε))),
  Piping.Admitted s → Piping.Reaches s tape t →
    Piping.ForwardShutdownSpec (Piping.observeShutdown t))

#check (@Piping.reaches_no_new_read :
  ∀ {α ε : Type} (s t : Piping.State α ε)
  (tape : List (Option (Piping.Decision α ε))),
  Piping.Admitted s → Piping.Reaches s tape t → t.source.nextRead = s.source.nextRead)

#check (@Piping.reaches_selection_stable :
  ∀ {α ε : Type} (s t : Piping.State α ε)
  (tape : List (Option (Piping.Decision α ε))) (p : Piping.ShutdownPlan ε),
  s.selection = some p → Piping.Reaches s tape t → t.selection = some p)

#check (@Piping.ready_frontier :
  ∀ {α ε : Type} (s : Piping.State α ε) (e : Boundary.Exception ε),
  s.phase = .readyToFinalize e →
    Piping.tick s = none ∧ ∀ d, Piping.decide s d = none)

#check (@Piping.preventAbort_write_rejection_no_override :
  ∀ {α ε : Type} (s t : Piping.State α ε)
  (tape : List (Option (Piping.Decision α ε))) (reason : Boundary.Exception ε),
  Piping.Admitted s → s.preventAbort = true → Piping.Reaches s tape t →
    t.phase = .readyToFinalize reason →
      ∃ p, t.selection = some p ∧ p.reason = reason ∧
        t.abortCall = none ∧ t.abortPromise = none)
