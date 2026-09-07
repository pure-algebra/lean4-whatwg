import Whatwg.Streams.Transform.Stream

/-!
# Transform consumer observations

TRANSFORM-PG-BACKPRESSURE fixes these local candidates. They retain actual P4
deliveries, component outcomes and consumer queries; the global DB-04 relation
is a separate open obligation. Canonical P4/P5 observations remain unchanged.
-/

namespace Whatwg.Streams.Transform

/-- Delivered readable chunks and both component outcomes, as a local output candidate. -/
structure OutputObservation (β ε : Type) where
  chunks : List β
  readableStatus : Readable.Status ε
  writableStatus : Writable.Status ε
  deriving Repr

/-- Consumer events of the coupled count-profile projection. -/
inductive VisibleEvent (β ε : Type) where
  | readableSettlement (settlement : Readable.Settlement β ε)
  | readableDesiredSize (value : Option Readable.Size)
  | writable (event : Writable.VisibleEvent ε)
  | enqueueReturned (call : Nat) (result : Except (Boundary.Exception ε) Unit)
  deriving Repr

/-- The output candidate together with ordered consumer events; not yet the global M2 mask. -/
structure OrderedObservation (β ε : Type) where
  output : OutputObservation β ε
  events : List (VisibleEvent β ε)
  deriving Repr

/-- Filter only this transform view's administrative/internal events, retaining public returns. -/
def visibleEvent {α β ε : Type} (internalIds : List Nat) :
    Event α β ε → Option (VisibleEvent β ε)
  | .readable (.settled x) => some (.readableSettlement x)
  | .readable (.desiredSizeRead x) => some (.readableDesiredSize x)
  | .writable (.settled id result) =>
      if id ∈ internalIds then none else some (.writable (.settled id result))
  | .writable (.returned call promise) => some (.writable (.returned call promise))
  | .writable (.readyRead call promise) => some (.writable (.readyRead call promise))
  | .writable (.closedRead call promise) => some (.writable (.closedRead call promise))
  | .writable (.desiredSizeRead call value) => some (.writable (.desiredSizeRead call value))
  | .writable (.controllerReturned call) => some (.writable (.controllerReturned call))
  | .enqueueReturned call result => some (.enqueueReturned call result)
  | _ => none

/-- Derive output from actual P4 deliveries and the two canonical status projections. -/
def observeOutput {α β ε : Type} (s : State α β ε) : OutputObservation β ε :=
  ⟨(Readable.observeM1 s.readable).1, s.readable.status, s.writable.status⟩

/-- Ordered consumer view with internal settlement filtering confined to this projection. -/
def observeOrdered {α β ε : Type} (s : State α β ε) : OrderedObservation β ε :=
  ⟨observeOutput s, s.trace.filterMap (visibleEvent s.internalPromises)⟩

end Whatwg.Streams.Transform
