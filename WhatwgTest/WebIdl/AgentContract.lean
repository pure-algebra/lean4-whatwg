import Whatwg.WebIdl
import WhatwgTest.Audit.Freeze

/-!
Breaker-owned Q5 battery for slice B3: the Web IDL promise verbs over the
ECMAScript agent, their views onto the frozen store-level operations of
`Whatwg.WebIdl.Promise`, and the D46 law at the Web IDL surface.

Packet: `test/contracts/promise-agent-q5.contract.md`.
Graph: `PROMISE-PG-AGENT`, `docs/PROMISE-AGENT-DAG.md`.
Attacks: `test/counterexamples/promise/ATTACKS.md`, section "Q5 agent
packet", rows WS-PROM-CE-040..047.

Every ascription names a declaration that does not exist at `b0d35e2`: this
module is red until builder slice B3 lands `Whatwg/WebIdl/Agent.lean` and
imports it from `Whatwg/WebIdl.lean`. B3 depends on B1 only. The builder must
not change a statement in this file; it may repair the elaboration of an
`example`'s proof without changing the example's statement.

The landed `Whatwg.WebIdl.Promise.resolve` and `reject` keep their signatures
and statements (R-W3): they are the table views of the operations below
(`resolve_view`, `reject_view`), and no frozen ascription changes.

Byte spans are 0-based, ends exclusive, into
`vendor/whatwg-webidl-a652053f/index.bs`
(SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`).
Row ids are those of `generated/webidl-census.tsv`; citing one anchors a
declaration and moves no coverage state. Every Web IDL row here stays
`partial` at best: each has a step that converts an IDL value to an
ECMAScript value, which is the binding layer (`hostOnly`).

Masks are DB-04's, written "DB-04 M1" and "DB-04 M2"; no Lean name here
spells a mask.
-/

set_option autoImplicit false

open Whatwg.Ecma262

/-! ## 1. The verbs

`op.a-new-promise` (347604..347946), `op.resolve` (349216..349783),
`op.reject` (349785..350073), `op.dfn-perform-steps-once-promise-is-settled`
(350075..352408) with its step 6 capability, `op.upon-fulfillment`
(352410..352816), `op.upon-rejection` (352818..353237),
`op.mark-a-promise-as-handled` (356060..356713), `op.a-promise-resolved-with`
(347948..348631) and `op.a-promise-rejected-with` (348633..349214), each on its
non-thenable branch. Gap ids: `G-03`; `G-11` remainder for `react`'s derived
capability (step 6 and step 8, now present); `G-05` stays out. A Web IDL
promise value is the capability record `op.a-new-promise` returns
(`WS-PROM-CE-034`). -/

#whatwg_freeze (@Whatwg.WebIdl.Agent.newPromise :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body × Promise.Capability)
#whatwg_freeze (@Whatwg.WebIdl.Agent.resolve :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability →
    value → Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.WebIdl.Agent.reject :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability →
    reason → Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.WebIdl.Agent.react :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability →
    Option body → Option body →
    Agent.Agent value reason body × Option (Option Promise.Capability))
#whatwg_freeze (@Whatwg.WebIdl.Agent.uponFulfillment :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability →
    body → Agent.Agent value reason body × Option (Option Promise.Capability))
#whatwg_freeze (@Whatwg.WebIdl.Agent.uponRejection :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability →
    body → Agent.Agent value reason body × Option (Option Promise.Capability))
#whatwg_freeze (@Whatwg.WebIdl.Agent.markAsHandled :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability →
    Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.WebIdl.Agent.resolvedWith :
  ∀ {value reason body : Type}, Agent.Agent value reason body → value →
    Agent.Agent value reason body × Promise.Capability)
#whatwg_freeze (@Whatwg.WebIdl.Agent.rejectedWith :
  ∀ {value reason body : Type}, Agent.Agent value reason body → reason →
    Agent.Agent value reason body × Promise.Capability)

/-! ## 2. Defining equations: thin wrappers, minting no state of their own

DB-04 M1 for all nine. `uponFulfillment` and `uponRejection` keep the landed
`G-11` modelling restriction: the other handler is `none` (`WS-PROM-CE-036`). -/

#whatwg_freeze (@Whatwg.WebIdl.Agent.newPromise_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Whatwg.WebIdl.Agent.newPromise a = Agent.newPromise a) axioms []
#whatwg_freeze (@Whatwg.WebIdl.Agent.resolve_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (v : value),
    Whatwg.WebIdl.Agent.resolve a p v = Agent.resolve a p v) axioms [propext]
#whatwg_freeze (@Whatwg.WebIdl.Agent.reject_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (r : reason),
    Whatwg.WebIdl.Agent.reject a p r = Agent.reject a p r) axioms [propext]
#whatwg_freeze (@Whatwg.WebIdl.Agent.react_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (onFulfilled onRejected : Option body),
    Whatwg.WebIdl.Agent.react a p onFulfilled onRejected =
      Agent.perform a p.promise onFulfilled onRejected true) axioms []
#whatwg_freeze (@Whatwg.WebIdl.Agent.uponFulfillment_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (steps : body),
    Whatwg.WebIdl.Agent.uponFulfillment a p steps =
      Whatwg.WebIdl.Agent.react a p (some steps) none) axioms []
#whatwg_freeze (@Whatwg.WebIdl.Agent.uponRejection_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (steps : body),
    Whatwg.WebIdl.Agent.uponRejection a p steps =
      Whatwg.WebIdl.Agent.react a p none (some steps)) axioms []
#whatwg_freeze (@Whatwg.WebIdl.Agent.markAsHandled_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability),
    Whatwg.WebIdl.Agent.markAsHandled a p = Agent.markHandled a p.promise) axioms []
#whatwg_freeze (@Whatwg.WebIdl.Agent.resolvedWith_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (v : value),
    Whatwg.WebIdl.Agent.resolvedWith a v =
      (Whatwg.WebIdl.Agent.resolve (Whatwg.WebIdl.Agent.newPromise a).1
          (Whatwg.WebIdl.Agent.newPromise a).2 v,
        (Whatwg.WebIdl.Agent.newPromise a).2)) axioms [propext]
#whatwg_freeze (@Whatwg.WebIdl.Agent.rejectedWith_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (r : reason),
    Whatwg.WebIdl.Agent.rejectedWith a r =
      (Whatwg.WebIdl.Agent.reject (Whatwg.WebIdl.Agent.newPromise a).1
          (Whatwg.WebIdl.Agent.newPromise a).2 r,
        (Whatwg.WebIdl.Agent.newPromise a).2)) axioms [propext]

/-! ## 3. The frozen store-level operations are views

Each right side is the landed `Whatwg.WebIdl.Promise` operation. DB-04 M1.
`resolve_view` and `reject_view` are D46's re-description: the frozen
`resolve` and `reject` are what the agent's verbs do to the table, for a
capability the agent stored, under `WF`. -/

#whatwg_freeze (@Whatwg.WebIdl.Agent.newPromise_view :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    (Whatwg.WebIdl.Agent.newPromise a).1.table =
        (Whatwg.WebIdl.Promise.newPromiseWithCapability a.table a.nextFunction).1 ∧
      (Whatwg.WebIdl.Agent.newPromise a).2 =
        (Whatwg.WebIdl.Promise.newPromiseWithCapability a.table a.nextFunction).2) axioms []
#whatwg_freeze (@Whatwg.WebIdl.Agent.markAsHandled_view :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability),
    (Whatwg.WebIdl.Agent.markAsHandled a p).table =
      Whatwg.WebIdl.Promise.markAsHandled a.table p.promise) axioms []
#whatwg_freeze (@Whatwg.WebIdl.Agent.resolve_view :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (f : Promise.ResolvingFunctions) (v : value),
    Agent.WF a →
      a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == p.resolve) =
        some f →
      f.promise = p.promise →
      (Whatwg.WebIdl.Agent.resolve a p v).table =
        Whatwg.WebIdl.Promise.resolve a.table p.promise v) axioms [propext]
#whatwg_freeze (@Whatwg.WebIdl.Agent.reject_view :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (p : Promise.Capability) (f : Promise.ResolvingFunctions) (r : reason),
    Agent.WF a →
      a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.reject == p.reject) =
        some f →
      f.promise = p.promise →
      (Whatwg.WebIdl.Agent.reject a p r).table =
        Whatwg.WebIdl.Promise.reject a.table p.promise r) axioms [propext]

/-! ## 4. D46 at the Web IDL surface

"react" then "resolve" on a pending promise whose functions have not fired
enqueues, behind every job already queued and every reaction already waiting,
exactly the new reaction's job. DB-04 M2: it observes queue order. -/

#whatwg_freeze (@Whatwg.WebIdl.Agent.react_resolve :
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
          [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)])) axioms [propext, Quot.sound]

/-! ## 5. `WS-PROM-CE-040`, the seed witness of the design's §3.3

Finite and decidable over `Unit`, `Nat` and `Nat`, closed by `rfl`. -/

namespace WhatwgTest.WebIdl.AgentContract

/-- One pending promise with its capability, from the empty agent. -/
def start : Agent.Agent Unit Nat Nat × Promise.Capability :=
  Whatwg.WebIdl.Agent.newPromise Agent.empty

/-- Store level, the attack: `WebIdl.Promise.react` on the table, reactions and
queue, then `WebIdl.Promise.resolve` on the table. `resolve` takes no queue, so
the queue `react` returned is the only queue there is, and it is empty. -/
example :
    (match Whatwg.WebIdl.Promise.react start.1.table start.1.reactions start.1.queue
        start.2.promise (some 7) none with
      | none => 99
      | some res => res.2.2.1.pending.length) = 0 := rfl

/-- The store-level `resolve` does settle the promise: the job is what is
missing, not the settlement. -/
example :
    (match Whatwg.WebIdl.Promise.react start.1.table start.1.reactions start.1.queue
        start.2.promise (some 7) none with
      | none => none
      | some res =>
          Promise.Table.get (Whatwg.WebIdl.Promise.resolve res.1 start.2.promise ())
            start.2.promise) = some (Promise.State.fulfilled ()) := rfl

/-- Agent level, the repair: the same two verbs enqueue exactly the reaction's
job. -/
example :
    (Whatwg.WebIdl.Agent.resolve (Whatwg.WebIdl.Agent.react start.1 start.2 (some 7) none).1
        start.2 ()).queue.pending =
      [Jobs.ReactionJob.mk 0 (Except.ok ())] := rfl

/-- `react` answers the derived capability, whose promise is pending. -/
example :
    (Whatwg.WebIdl.Agent.react start.1 start.2 (some 7) none).2 =
        some (some (Promise.Capability.mk 1 2 3)) ∧
      (Whatwg.WebIdl.Agent.react start.1 start.2 (some 7) none).1.table.get 1 =
        some Promise.State.pending := ⟨rfl, rfl⟩

/-- "a promise resolved with" settles through the stored functions, so a second
`reject` through the same capability is inert. -/
example :
    (Whatwg.WebIdl.Agent.resolvedWith (Agent.empty : Agent.Agent Unit Nat Nat) ()).1.table.get 0 =
        some (Promise.State.fulfilled ()) ∧
      Whatwg.WebIdl.Agent.reject
          (Whatwg.WebIdl.Agent.resolvedWith (Agent.empty : Agent.Agent Unit Nat Nat) ()).1
          (Whatwg.WebIdl.Agent.resolvedWith (Agent.empty : Agent.Agent Unit Nat Nat) ()).2 9 =
        (Whatwg.WebIdl.Agent.resolvedWith (Agent.empty : Agent.Agent Unit Nat Nat) ()).1 :=
  ⟨rfl, rfl⟩

end WhatwgTest.WebIdl.AgentContract
