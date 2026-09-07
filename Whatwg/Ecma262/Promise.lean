/-!
# ECMAScript promise objects

Reserved for the Promise Objects clause of the pinned ES2026 source: the
`[[PromiseState]]`, `[[PromiseResult]]`, `[[PromiseFulfillReactions]]`,
`[[PromiseRejectReactions]]` and `[[PromiseIsHandled]]` slots as first-order
state, PromiseCapability and PromiseReaction records, the resolving
functions, `PerformPromiseThen`, `NewPromiseResolveThenableJob`, and the
abstract operations the `then`/`catch`/`finally` and combinator methods are
written over. Thenables and host bookkeeping (`HostPromiseRejectionTracker`)
are foreign boundaries with profiles. Declaration-free; the P8 plan owns the
first packet.
-/
