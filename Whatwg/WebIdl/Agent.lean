import Whatwg.Ecma262.Agent
import Whatwg.WebIdl.Promise

/-!
# Web IDL promise verbs over the ECMAScript agent

Owner: promise slice Q5 (ruling R-W3), graph `PROMISE-PG-AGENT`
(`docs/PROMISE-AGENT-DAG.md`), at the surface
`test/contracts/promise-agent-q5.contract.md` freezes (ruling R-W13). This
module is builder slice B3; its battery is
`WhatwgTest/WebIdl/AgentContract.lean`.

Landed here: the Web IDL Promises verbs over the agent record
`Whatwg.Ecma262.Agent.Agent`: "a new promise", "resolve", "reject", "react"
with the capability of its step 6, "upon fulfillment", "upon rejection", "mark
as handled", "a promise resolved with" and "a promise rejected with". A Web IDL
promise value is the PromiseCapability Record "a new promise" returns
(`WS-PROM-CE-034`). Every verb is an adapter: one agent operation, or two in
sequence, and this module mints no state of its own.

Relation to the landed store-level verbs of `Whatwg.WebIdl.Promise`, which keep
their statements and bodies (ruling R-W3): they are the table views of the
verbs here, and `newPromise_view`, `markAsHandled_view`, `resolve_view` and
`reject_view` say so, each right side the landed operation. Debt D46 is why the
agent-level verbs exist: the store-level `resolve` is `Table.settle`, whose
signature carries no reaction store and no queue, so "react" followed by
"resolve" enqueues no reaction job there (`WS-PROM-CE-040`). Here `resolve`
calls the capability's stored resolving functions, which settle the promise and
trigger its reactions, and `react_resolve` is the law.

Not modelled, with gap ids: the binding layer, every conversion between an IDL
value and an ECMAScript value, which stays `hostOnly`, so every census row
cited here stays `partial` at best; the realm of "a new promise" and of "react"
step 5 (`G-07` remainder); thenable adoption (`G-05`), so "resolve" and "a
promise resolved with" take the non-thenable branch; and the two built-in
functions "react" steps 1 to 4 create (`G-11` remainder): a missing set of
steps is an empty handler (`none`), as the landed `Promise.react` has it
(`WS-PROM-CE-036`), and `react` names the consequence.

Masks are DB-04's, written "DB-04 M1" and "DB-04 M2"; no declaration here
spells a mask. Every Web IDL census row cited here, with its span into
`vendor/whatwg-webidl-a652053f/index.bs` and the span's SHA-256, anchors a
declaration and is never a numerator: `generated/webidl-census.tsv` is
unchanged, and no coverage state moves.

Layering (DB-11): this module imports `Whatwg.Ecma262.Agent` and
`Whatwg.WebIdl.Promise`, and through them `Whatwg.Ecma262`; no `Effects` module
and no `Whatwg.Infra` module (R-W3). Inside this namespace an unqualified
`Agent.resolve` names this module's `resolve`, so every agent operation below
is written `Whatwg.Ecma262.Agent.…` in full.
-/

namespace Whatwg.WebIdl.Agent

open Whatwg.Ecma262

/-! ## 1. The verbs -/

/-- `op.a-new-promise` (NEWP, 347604..347946, digest
`a9c212f9448d6cfdaf262e33f33ed5104392aaec738b6e3ae22b285edc3751b3`): step 2,
`NewPromiseCapability(%Promise%)`, as the agent's `newPromise`, which allocates
a pending promise, stores its two resolving functions and answers the
capability. The realm of step 1 is not modelled (`G-07` remainder). Adapter. -/
def newPromise {value reason body : Type} (a : Agent.Agent value reason body) :
    Agent.Agent value reason body × Promise.Capability :=
  Whatwg.Ecma262.Agent.newPromise a

/-- `op.resolve` (RESOLVE, 349216..349783, digest
`071c11c45c5c1da04b86837e7911385b64880eaf3a013ff769676110af545cc3`): step 3,
`Call(p.[[Resolve]], undefined, « value »)`, as the agent's `resolve`, which
calls the stored resolving function of `p`'s `[[Resolve]]` identity, so the
promise settles and its waiting reactions enqueue their jobs (debt D46). Step 1
is the caller's: `v` is always given, and a `Promise<undefined>` caller passes
the value that stands for *undefined*. Step 2's conversion is the binding
layer. A capability whose functions this agent never stored is inert
(`WS-PROM-CE-041`), a case the text has no counterpart for. Adapter. -/
def resolve {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (v : value) : Agent.Agent value reason body :=
  Whatwg.Ecma262.Agent.resolve a p v

/-- `op.reject` (REJECTOP, 349785..350073, digest
`c2edaaba6c2c29a161365819f857be96eabcf9ee573580a4687e8eec72a900ea`): step 1,
`Call(p.[[Reject]], undefined, « r »)`, as the agent's `reject`, through the
stored function of `p`'s `[[Reject]]` identity, whose one-shot marker is the
one `resolve` reads (`WS-PROM-CE-042`). Adapter. -/
def reject {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (r : reason) : Agent.Agent value reason body :=
  Whatwg.Ecma262.Agent.reject a p r

/-- `op.dfn-perform-steps-once-promise-is-settled` (REACT, 350075..352408,
digest `dd0e08ae5b8739280837b31e10f2ace6f1a7f9b20034124d7c748d450aaab383`):
step 6 mints `newCapability`, step 7 performs `PerformPromiseThen` on
`p.[[Promise]]` with it, and step 8 returns it, which is the agent's `perform`
with `derive` set. The answer is `some (some newCapability)` when `p`'s promise
is allocated; a missing promise answers `none` and leaves the agent unchanged,
where the text has no such case (`E-31`'s `Option`).

Steps 1 to 4 are not modelled (`G-11` remainder): the two sets of steps are
first-order handler descriptors, never built-in functions, and a missing set is
an empty handler (`none`, `PerformPromiseThen` steps 3 and 5). The text instead
builds both functions, and its rejection function without steps returns "a
promise rejected with" the reason, which the derived promise then adopts. Both
end with the derived promise rejected with that reason (DB-04 M1); the text
allocates one more promise and settles the derived one later, through thenable
adoption (`G-05`), so DB-04 M2 is not claimed for a missing rejection handler
(`WS-PROM-CE-036`). Adapter. -/
def react {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (onFulfilled onRejected : Option body) :
    Agent.Agent value reason body × Option (Option Promise.Capability) :=
  Whatwg.Ecma262.Agent.perform a p.promise onFulfilled onRejected true

/-- `op.upon-fulfillment` (UPONF, 352410..352816, digest
`81ccd0a141715f38ae30f05c97a994c4ea3fef748c6301da8f3b8e4c6c785b9d`): "react"
with `steps` run on fulfilment and no rejection steps, which `react` models as
an empty handler; the landed `G-11` restriction of `Promise.uponFulfillment`
carries over unchanged (`WS-PROM-CE-036`). Adapter. -/
def uponFulfillment {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (steps : body) :
    Agent.Agent value reason body × Option (Option Promise.Capability) :=
  react a p (some steps) none

/-- `op.upon-rejection` (UPONR, 352818..353237, digest
`f1e47b988febfd3652dac64ddb390db465d96a07f5b2d939cd8c62413221e7e9`): "react"
with `steps` run on rejection and an empty fulfilment handler, which passes the
value through as the text's fulfilment function without steps does. Adapter. -/
def uponRejection {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (steps : body) :
    Agent.Agent value reason body × Option (Option Promise.Capability) :=
  react a p none (some steps)

/-- `op.mark-a-promise-as-handled` (HANDLEDOP, 356060..356713, digest
`644263e9155cf45d31167e53346f9d0e2431aedde301b440dbc92d9021b618bc`): set
`p.[[Promise]].[[PromiseIsHandled]]` to true, the agent's `markHandled`. A
missing promise leaves the agent unchanged. The handled bit is read by nothing
(`G-02` remainder). Adapter. -/
def markAsHandled {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) : Agent.Agent value reason body :=
  Whatwg.Ecma262.Agent.markHandled a p.promise

/-- `op.a-promise-resolved-with` (RESOLVEDW, 347948..348631, digest
`a5b86f19962066ef9844df3f2ee2494cb78c74bae6cf6690cc8ee1b6e0b60015`): steps 3 to
5, a new capability, then `Call(promiseCapability.[[Resolve]], « value »)`
through its stored functions, then the capability; the answer is the agent
after both and the capability. Step 1's conversion is the binding layer, and a
thenable `value` is out (`G-05`). Adapter. -/
def resolvedWith {value reason body : Type} (a : Agent.Agent value reason body) (v : value) :
    Agent.Agent value reason body × Promise.Capability :=
  (resolve (newPromise a).1 (newPromise a).2 v, (newPromise a).2)

/-- `op.a-promise-rejected-with` (REJECTEDW, 348633..349214, digest
`3f6d84e5da374f56e56aebba956939b54dbefb219a67137a37128ecce58f20f8`): steps 2 to
4, a new capability, then `Call(promiseCapability.[[Reject]], « r »)` through
its stored functions, then the capability. Adapter. -/
def rejectedWith {value reason body : Type} (a : Agent.Agent value reason body) (r : reason) :
    Agent.Agent value reason body × Promise.Capability :=
  (reject (newPromise a).1 (newPromise a).2 r, (newPromise a).2)

/-! ## 2. Defining equations

Each verb is the agent operation it wraps, or "react" at a fixed handler, so no
verb mints state of its own. DB-04 M1 for all nine: each states which
operation runs, not what it does to the queue or the trace. -/

/-- "A new promise" is the agent's `newPromise`. Defining equation
(`op.a-new-promise`); DB-04 M1. -/
theorem newPromise_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Whatwg.WebIdl.Agent.newPromise a = Whatwg.Ecma262.Agent.newPromise a := by
  intros; rfl

/-- "Resolve" is the agent's `resolve`. Defining equation (`op.resolve`); DB-04
M1. -/
theorem resolve_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability) (v : value),
      Whatwg.WebIdl.Agent.resolve a p v = Whatwg.Ecma262.Agent.resolve a p v := by
  intros; rfl

/-- "Reject" is the agent's `reject`. Defining equation (`op.reject`); DB-04
M1. -/
theorem reject_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability) (r : reason),
      Whatwg.WebIdl.Agent.reject a p r = Whatwg.Ecma262.Agent.reject a p r := by
  intros; rfl

/-- "React" is the agent's `perform` on `p`'s promise with a derived capability.
Defining equation (`op.dfn-perform-steps-once-promise-is-settled`); DB-04 M1. -/
theorem react_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability) (onFulfilled onRejected : Option body),
      Whatwg.WebIdl.Agent.react a p onFulfilled onRejected =
        Whatwg.Ecma262.Agent.perform a p.promise onFulfilled onRejected true := by
  intros; rfl

/-- "Upon fulfillment" is "react" with an empty rejection handler. Defining
equation (`op.upon-fulfillment`); DB-04 M1. -/
theorem uponFulfillment_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability) (steps : body),
      Whatwg.WebIdl.Agent.uponFulfillment a p steps =
        Whatwg.WebIdl.Agent.react a p (some steps) none := by
  intros; rfl

/-- "Upon rejection" is "react" with an empty fulfilment handler. Defining
equation (`op.upon-rejection`); DB-04 M1. -/
theorem uponRejection_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability) (steps : body),
      Whatwg.WebIdl.Agent.uponRejection a p steps =
        Whatwg.WebIdl.Agent.react a p none (some steps) := by
  intros; rfl

/-- "Mark as handled" is the agent's `markHandled` on `p`'s promise. Defining
equation (`op.mark-a-promise-as-handled`); DB-04 M1. -/
theorem markAsHandled_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability),
      Whatwg.WebIdl.Agent.markAsHandled a p = Whatwg.Ecma262.Agent.markHandled a p.promise := by
  intros; rfl

/-- "A promise resolved with" is "a new promise" and then "resolve" through the
new capability. Defining equation (`op.a-promise-resolved-with`); DB-04 M1. -/
theorem resolvedWith_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (v : value),
      Whatwg.WebIdl.Agent.resolvedWith a v =
        (Whatwg.WebIdl.Agent.resolve (Whatwg.WebIdl.Agent.newPromise a).1
            (Whatwg.WebIdl.Agent.newPromise a).2 v,
          (Whatwg.WebIdl.Agent.newPromise a).2) := by
  intros; rfl

/-- "A promise rejected with" is "a new promise" and then "reject" through the
new capability. Defining equation (`op.a-promise-rejected-with`); DB-04 M1. -/
theorem rejectedWith_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (r : reason),
      Whatwg.WebIdl.Agent.rejectedWith a r =
        (Whatwg.WebIdl.Agent.reject (Whatwg.WebIdl.Agent.newPromise a).1
            (Whatwg.WebIdl.Agent.newPromise a).2 r,
          (Whatwg.WebIdl.Agent.newPromise a).2) := by
  intros; rfl

/-! ## 3. The landed store-level verbs are views

Each right side is the landed `Whatwg.WebIdl.Promise` operation, not a copy.
`resolve_view` and `reject_view` are D46's re-description: the frozen `resolve`
and `reject` are what the agent's verbs do to the table, for a capability whose
functions the agent stored, under `WF`. DB-04 M1 for all four: each observes the
table only. -/

/-- The table and capability of "a new promise" are the landed
`Promise.newPromiseWithCapability`'s at the function cursor. View
(`op.a-new-promise`); DB-04 M1. -/
theorem newPromise_view :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      (Whatwg.WebIdl.Agent.newPromise a).1.table =
          (Whatwg.WebIdl.Promise.newPromiseWithCapability a.table a.nextFunction).1 ∧
        (Whatwg.WebIdl.Agent.newPromise a).2 =
          (Whatwg.WebIdl.Promise.newPromiseWithCapability a.table a.nextFunction).2 := by
  intros; exact ⟨rfl, rfl⟩

/-- The table "mark as handled" leaves is the landed `Promise.markAsHandled`'s.
View (`op.mark-a-promise-as-handled`); DB-04 M1. -/
theorem markAsHandled_view :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability),
      (Whatwg.WebIdl.Agent.markAsHandled a p).table =
        Whatwg.WebIdl.Promise.markAsHandled a.table p.promise := by
  intros; rfl

/-- **D46 re-described.** For a capability whose resolving function this agent
stored, under `WF`, "resolve" changes the table exactly as the landed
store-level `Promise.resolve` does; a function that already fired is covered by
`WF.resolvedSettled`, where both sides leave the table as it is. One appeal to
`Whatwg.Ecma262.Agent.resolve_table`. Bridge (`op.resolve`); DB-04 M1. -/
theorem resolve_view :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability) (f : Promise.ResolvingFunctions) (v : value),
      Agent.WF a →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == p.resolve) =
          some f →
        f.promise = p.promise →
        (Whatwg.WebIdl.Agent.resolve a p v).table =
          Whatwg.WebIdl.Promise.resolve a.table p.promise v := by
  intro value reason body a p f v hw hf hfp
  exact Whatwg.Ecma262.Agent.resolve_table a p f v hw hf hfp

/-- The same for "reject", found by the `[[Reject]]` identity: the landed
store-level `Promise.reject` is its table view. One appeal to
`Whatwg.Ecma262.Agent.reject_table`. Bridge (`op.reject`); DB-04 M1. -/
theorem reject_view :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability) (f : Promise.ResolvingFunctions) (r : reason),
      Agent.WF a →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.reject == p.reject) =
          some f →
        f.promise = p.promise →
        (Whatwg.WebIdl.Agent.reject a p r).table =
          Whatwg.WebIdl.Promise.reject a.table p.promise r := by
  intro value reason body a p f r hw hf hfp
  exact Whatwg.Ecma262.Agent.reject_table a p f r hw hf hfp

/-! ## 4. D46 at the Web IDL surface -/

/-- **D46.** "React" with fulfilment steps and then "resolve", on a pending
promise whose resolving functions are stored and unfired: behind every job
already queued, the jobs of the reactions already waiting on that promise, in
registration order, and then exactly the new reaction's job. The store-level
`Promise.react` and `Promise.resolve` enqueue none of them
(`WS-PROM-CE-040`). One appeal to
`Whatwg.Ecma262.Agent.react_resolve_enqueues_wf`. Law (`op.resolve`,
`op.dfn-perform-steps-once-promise-is-settled`); DB-04 M2, since it observes
queue order. -/
theorem react_resolve :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (p : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value),
      Agent.WF a → a.table.get p.promise = some Promise.State.pending →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == p.resolve) =
          some f →
        f.alreadyResolved = false → f.promise = p.promise →
        (Whatwg.WebIdl.Agent.resolve (Whatwg.WebIdl.Agent.react a p (some h) none).1 p
            v).queue.pending =
          a.queue.pending ++
            ((Promise.Reactions.waitingOn a.reactions p.promise
                Promise.ReactionType.fulfill).map
              (fun (r : Promise.Reaction body) => Jobs.ReactionJob.mk r.id (Except.ok v)) ++
            [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)]) := by
  intro value reason body a p f h v hw hp hf hfr hfp
  exact Whatwg.Ecma262.Agent.react_resolve_enqueues_wf a p f h v hw hp hf hfr hfp

end Whatwg.WebIdl.Agent
