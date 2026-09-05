import Whatwg.Streams.Piping.PipeTo

/-!
# Forward-error candidate transitions

PIPING-PG-FORWARD-SHUTDOWN fixes this local deterministic schedule over
canonical P5 operations. Its finite relational judgment has no fuel
parameter; global scheduling and full pipe finalization remain open.
-/

namespace Whatwg.Streams.Piping

/-- External source error and actual writable foreign boundaries; no new-read decision. -/
inductive Decision (α ε : Type) where
  | sourceError (reason : Boundary.Exception ε)
  | writable (decision : Writable.Decision α ε)

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def stepWritable {α ε : Type} (s : State α ε) (d : Option (Writable.Decision α ε)) :
    Option (State α ε) :=
  (match d with
    | none => Writable.tick s.destination
    | some a => Writable.decide s.destination a).map
    (fun w => emit s (.writable d) { s with destination := w })

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def externalFrontier {α ε : Type} (s : State α ε) : Bool :=
  (match s.phase with
     | .readyToFinalize _ => false
     | _ => if Writable.externalFrontier s.destination then
         match s.destination.control with
         | [] => match s.phase with
             | .running | .waitingWrites | .waitingAbort => true
             | _ => false
         | _ => true
       else false)

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def decide {α ε : Type} (s : State α ε) (d : Decision α ε) : Option (State α ε) :=
  (if externalFrontier s then match d with
     | .sourceError e => some (emit s (.sourceError e)
         { s with source := Readable.error s.source e })
     | .writable a => if foreignDecision a then stepWritable s (some a) else none
     else none)

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def tick {α ε : Type} (s : State α ε) : Option (State α ε) :=
  let action := fun p : ShutdownPlan ε =>
    if p.preventAbort then some (requestFinalize s p.reason)
    else invokeAbort s p
  match s.phase with
  | .readyToFinalize _ => none
  | _ => if s.destination.control ≠ [] then stepWritable s none
    else match s.phase with
    | .running => match s.source.status with
        | .errored _ => some (enterForwardShutdown s)
        | .readable =>
            match s.destination.status with
            | .writable =>
              if Writable.closeQueuedOrInFlight s.destination then stepWritable s none
              else match Writable.desiredSize s.destination, nextUnwritten s.links with
                | some size, some l =>
                    if Readable.sizePositive size then invokeWrite s l
                    else stepWritable s none
                | _, _ => stepWritable s none
            | _ => stepWritable s none
        | .closed => stepWritable s none
    | .draining => match s.selection with
        | none => none
        | some p =>
            if p.drainRequired then match nextUnwritten s.links with
              | some l => invokeWrite s l
              | none => some (emit s .administrative { s with phase := .waitingWrites })
            else action p
    | .returningWrite id call => captureWrite s id call
    | .waitingWrites => match s.selection with
        | none => none
        | some p => if allWrittenSettled s.destination s.links then action p
            else stepWritable s none
    | .returningAbort call => captureAbort s call
    | .waitingAbort => match s.selection, s.abortPromise with
        | some p, some id => match Writable.lookupPromise s.destination id with
            | some (.fulfilled _) => some (requestFinalize s p.reason)
            | some (.rejected reason) => some (requestFinalize s reason)
            | _ => stepWritable s none
        | _, _ => none
    | .readyToFinalize _ => none

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def Step {α ε : Type} (s : State α ε) (d : Option (Decision α ε)) (t : State α ε) : Prop :=
  (match d with | none => tick s | some a => decide s a) = some t

/-- Finite candidate runs; the requirements predicate is separately defined in Requirements. -/
inductive Reaches {α ε : Type} :
    State α ε → List (Option (Decision α ε)) → State α ε → Prop
  | nil (s : State α ε) : Reaches s [] s
  | cons {s middle last : State α ε} {d : Option (Decision α ε)}
      {ds : List (Option (Decision α ε))} :
      Step s d middle → Reaches middle ds last → Reaches s (d :: ds) last

end Whatwg.Streams.Piping
