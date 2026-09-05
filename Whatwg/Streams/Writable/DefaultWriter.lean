import Whatwg.Streams.Writable.DefaultController

/-!
# Writable.DefaultWriter.lean

Owner: the `WritableStreamDefaultWriter` state: its ready and closed
promises, the desired size it reports, and the write, close, abort and
release operations.

Spec anchors: `default-writer-class`, `default-writer-internal-slots`,
`ws-writer-abstract-ops`.

Opens in P5.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-!
The P2 note above is historical. The frozen WRITABLE-PG-DEFAULT dispatcher
admits external calls only at an external frontier, retaining suspended callbacks.
Its observations are the local candidate views; their DB-04 embeddings remain open.
-/

namespace Whatwg.Streams.Writable

/--
Dispatch the frozen write/close/abort and query algorithms at an external frontier.
`op.writable-stream-default-writer-write` owns write entry; the remaining census
anchors and exact return equations are recorded in WRITABLE-PG-DEFAULT.
-/
def decide {α ε : Type} (s : State α ε) (d : Decision α ε) : Option (State α ε) :=
  if externalFrontier s then
    match d with
    | .write chunk =>
        some { s with
          nextCall := s.nextCall + 1, control := .getSize s.nextCall chunk :: s.control }
    | .close =>
        some { s with
          nextCall := s.nextCall + 1, control := .beginClose s.nextCall :: s.control }
    | .abort reason =>
        some { s with
          nextCall := s.nextCall + 1, control := .beginAbort s.nextCall reason :: s.control }
    | .controllerError reason =>
        some { s with
          nextCall := s.nextCall + 1,
          control := .controllerError reason :: .returnUnit s.nextCall :: s.control }
    | .queryReady =>
        some { s with
          nextCall := s.nextCall + 1, trace := s.trace ++ [.readyRead s.nextCall s.readyPromise] }
    | .queryClosed =>
        some { s with
          nextCall := s.nextCall + 1, trace := s.trace ++ [.closedRead s.nextCall s.closedPromise] }
    | .queryDesiredSize =>
        some { s with
          nextCall := s.nextCall + 1,
          trace := s.trace ++ [.desiredSizeRead s.nextCall (desiredSize s)] }
    | .answer kind id answer => acceptAnswer s kind id answer
    | .returnSize answer =>
        match s.control with
        | .awaitSize call chunk :: tail =>
            some { s with control := match answer with
              | .value size => .afterSize call chunk size :: tail
              | .thrown reason => .errorIfNeeded reason :: .afterSize call chunk sizes.one :: tail }
        | _ => none
    | .returnSink result =>
        match s.control with
        | .awaitSink op :: tail =>
            if operationPhase s (operationKind op) (operationRequest op) = some .invoking then
              some (attachSink { s with control := tail } op result)
            else none
        | _ => none
    | .returnSignal =>
        match s.control with
        | .awaitSignal call reason :: tail =>
            some { s with control := .afterSignal call reason :: tail }
        | _ => none
  else none

end Whatwg.Streams.Writable
