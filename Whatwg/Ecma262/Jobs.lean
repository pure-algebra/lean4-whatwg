/-!
# ECMAScript jobs and job queues

Reserved for the Jobs and Host Operations to Enqueue Jobs clause of the
pinned ES2026 source: Job Abstract Closures, `NewPromiseReactionJob`,
`HostEnqueuePromiseJob` and the ordering requirements the host must respect
(FIFO per realm, run to completion, only when the execution context stack is
empty). Ruling DB-03 models the queue as deterministic FIFO state inside the
configuration; this module is where that state and its enqueue/dequeue
operations will live, with HTML's microtask checkpoint as the host profile
that drains it. Declaration-free; the P8 plan owns the first packet.
-/
