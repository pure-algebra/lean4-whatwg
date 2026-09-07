import Whatwg.Streams.Readable.DefaultController

/-!
# Readable.DefaultReader.lean

Owner: the `ReadableStreamDefaultReader` state, its read requests as an
ordered list of pending answers, and the reader abstract operations that
fulfil or reject them.

Spec anchors: `default-reader-class`, `default-reader-internal-slots`,
`rs-reader-abstract-ops`.

Opens in P4.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-! The frozen P4a packet now supplies the post-start, fixed-reader implementation below. -/

namespace Whatwg.Streams.Readable

/-- `op.readable-stream-default-reader-read` and `op.rs-default-controller-private-pull`.
The already-dequeued chunk is saved across synchronous pull reentrancy, under local M1/M2. -/
def read {α ε : Type} (s : State α ε) : State α ε :=
  match s.status with
  | .closed =>
      { s with
        nextRead := s.nextRead + 1,
        readPromises := s.readPromises ++ [(s.nextRead, .fulfilled .done)],
        trace := s.trace ++ [.settled (.read s.nextRead (.ok .done))] }
  | .errored e =>
      { s with
        nextRead := s.nextRead + 1,
        readPromises := s.readPromises ++ [(s.nextRead, .rejected e)],
        trace := s.trace ++ [.settled (.read s.nextRead (.error e))] }
  | .readable =>
      match Data.dequeueValue sizes s.queue with
      | none =>
          callPullIfNeeded
            { s with
              nextRead := s.nextRead + 1,
              readPromises := s.readPromises ++ [(s.nextRead, .pending)],
              readRequests := s.readRequests ++ [s.nextRead] }
      | some (chunk, q) =>
          let t :=
            { s with
              queue := q, nextRead := s.nextRead + 1,
              readPromises := s.readPromises ++ [(s.nextRead, .pending)] }
          if s.closeRequested = true ∧ q.entries = [] then
            continuePull (streamClose { t with algorithms := none }) (.settleRead s.nextRead chunk)
          else callPullIfNeededWith t (.settleRead s.nextRead chunk)

end Whatwg.Streams.Readable
