import Whatwg.Ecma262

/-!
Breaker-owned Q5b battery for builder slice B5: the agent's stronger
invariant `Coherent`, the stronger order `Extends`, the two-state post
`postFrom` with the second adequacy judgment `ImplementsFrom`, the
`[[Reject]]` route and the dropped abrupt result of a reaction job, and the
reachability corollary.

Packet: `test/contracts/promise-agent-q5.contract.md`, section "Addendum
Q5b". Graph: `PROMISE-PG-AGENT`, `docs/PROMISE-AGENT-DAG.md`. Attacks:
`test/counterexamples/promise/ATTACKS.md`, section "Q5b agent addendum", rows
WS-PROM-CE-048 to WS-PROM-CE-056. Debts D62 and D65.

Every ascription names a declaration that does not exist at `5999363`: this
module is red until builder slice B5 lands `Whatwg/Ecma262/AgentInvariant.lean`
and imports it from `Whatwg/Ecma262.lean`. Nothing of Q5 changes: `WF`, `Le`,
`pre`, `post` and `Implements` keep their statements and bodies (rulings
R-W1(b) and R-W9), and every new name stands beside them.

The second judgment has the shape of `Agent.Implements`: from an agent the
stronger invariant holds of and a request `Agent.pre` admits, the step reaches
an agent later in the stronger order, of which the stronger invariant holds
again, and the answer satisfies the stronger post. The one difference is that
the stronger post reads both the agent the step starts from and the agent it
answers at, because "the head of the queue", "the running job's capability"
and "an unfired function" are facts of the earlier agent.

Masks are DB-04's, written "DB-04 M1" and "DB-04 M2"; no Lean name here
spells a mask. A law is DB-04 M2 when its statement observes the order of the
settlement trace or of the job queue, and DB-04 M1 otherwise; every law that
concludes `Extends` is DB-04 M2, through its `Le.trace` and `heldGrows`
clauses.
-/

set_option autoImplicit false

open Whatwg.Ecma262

/-! ## 1. The stronger invariant

`Coherent a` extends `WF a` with seven clauses. Each answers one gap of debts
D62 and D65 or keeps another clause inductive (contract, Addendum Q5b,
section B.2):

- `functionPromisesNodup` (keeps `unfiredPending` inductive): no two stored
  function records name one promise;
- `unfiredPending` (gap A): an unfired function's promise is pending;
- `settledTraced` (gap B): every settled cell is in the settlement trace with
  its result;
- `waitingPending` (gap C): a waiting reaction waits on a pending promise;
- `reactionsAllocated` (gap E): every registered or held reaction names an
  allocated promise;
- `listKinds` (keeps `jobsTyped` inductive): the fulfil list holds
  `~fulfill~` records and the reject list `~reject~` records;
- `jobsTyped` (gaps D and F): every queued job and the running job name a
  record, whose `[[Type]]` is the argument's tag and whose promise is settled
  with the argument. -/

#check (@Whatwg.Ecma262.Agent.Coherent :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Prop)

#check (@Whatwg.Ecma262.Agent.Coherent.toWF :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    Agent.WF a)
#check (@Whatwg.Ecma262.Agent.Coherent.functionPromisesNodup :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    (a.functions.map Promise.ResolvingFunctions.promise).Nodup)
#check (@Whatwg.Ecma262.Agent.Coherent.unfiredPending :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    ∀ f ∈ a.functions, f.alreadyResolved = false →
      Promise.Table.isPending a.table f.promise = true)
#check (@Whatwg.Ecma262.Agent.Coherent.settledTraced :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    (∀ (p : Nat) (v : value),
        Promise.Table.get a.table p = some (Promise.State.fulfilled v) →
          (p, Except.ok v) ∈ a.settlements) ∧
      (∀ (p : Nat) (r : reason),
        Promise.Table.get a.table p = some (Promise.State.rejected r) →
          (p, Except.error r) ∈ a.settlements))
#check (@Whatwg.Ecma262.Agent.Coherent.waitingPending :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject,
      r.phase = Promise.ReactionPhase.waiting →
        Promise.Table.get a.table r.promise = some Promise.State.pending)
#check (@Whatwg.Ecma262.Agent.Coherent.reactionsAllocated :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
      (a.table.getCell r.promise).isSome = true)
#check (@Whatwg.Ecma262.Agent.Coherent.listKinds :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    (∀ r ∈ a.reactions.fulfill, r.kind = Promise.ReactionType.fulfill) ∧
      (∀ r ∈ a.reactions.reject, r.kind = Promise.ReactionType.reject))
#check (@Whatwg.Ecma262.Agent.Coherent.jobsTyped :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    ∀ j : Agent.Job value reason, (j ∈ a.queue.pending ∨ a.running = some j) →
      ∃ r : Promise.Reaction body, Agent.reactionOf a j = some r ∧
        (∀ v : value, j.argument = Except.ok v →
          r.kind = Promise.ReactionType.fulfill ∧
            Promise.Table.get a.table r.promise = some (Promise.State.fulfilled v)) ∧
        (∀ e : reason, j.argument = Except.error e →
          r.kind = Promise.ReactionType.reject ∧
            Promise.Table.get a.table r.promise = some (Promise.State.rejected e)))

/-! ## 2. The stronger invariant is inductive

`Coherent.empty` and `Coherent.step` (every operation, enabled or disabled)
make it an invariant a consumer carries through its own proofs; reachability
follows. DB-04 M1. -/

#check (@Whatwg.Ecma262.Agent.Coherent.empty :
  ∀ {value reason body : Type},
    Agent.Coherent (Agent.empty : Agent.Agent value reason body))
#check (@Whatwg.Ecma262.Agent.Coherent.step :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (op : Agent.Op value reason body),
    Agent.Coherent a → Agent.Coherent (Agent.step a op).1)
#check (@Whatwg.Ecma262.Agent.Coherent.runOps :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (ops : List (Agent.Op value reason body)),
    Agent.Coherent a → Agent.Coherent (Agent.runOps a ops).1)
#check (@Whatwg.Ecma262.Agent.Coherent.reachable :
  ∀ {value reason body : Type} (ops : List (Agent.Op value reason body)),
    Agent.Coherent (Agent.runOps (Agent.empty : Agent.Agent value reason body) ops).1)

/-! ## 3. The stronger order (gap J)

`Extends a a'` extends `Le a a'`: besides the eight clauses of `Le`, a fired
function record survives unchanged, so a one-shot marker never clears, and
`held` only grows, at its end. Every operation moves up it. DB-04 M2. -/

#check (@Whatwg.Ecma262.Agent.Extends :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body → Prop)
#check (@Whatwg.Ecma262.Agent.Extends.toLe :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Extends a a' →
    Agent.Le a a')
#check (@Whatwg.Ecma262.Agent.Extends.markerKept :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Extends a a' →
    ∀ f ∈ a.functions, f.alreadyResolved = true → f ∈ a'.functions)
#check (@Whatwg.Ecma262.Agent.Extends.heldGrows :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Extends a a' →
    a.held <+: a'.held)

#check (@Whatwg.Ecma262.Agent.Extends.refl :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body), Agent.Extends a a)
#check (@Whatwg.Ecma262.Agent.Extends.trans :
  ∀ {value reason body : Type} {a b c : Agent.Agent value reason body},
    Agent.Extends a b → Agent.Extends b c → Agent.Extends a c)
#check (@Whatwg.Ecma262.Agent.Extends.step :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (op : Agent.Op value reason body),
    Agent.WF a → Agent.Extends a (Agent.step a op).1)

/-! ## 4. The two-state post

`postFrom a a' op c ans`: the Q5 post at the answering agent `a'`, and what
the step did relative to the agent `a` it started from. Gap A: `resolve` and
`reject` through an unfired stored function fulfil or reject the promise with
the request's value or reason. Gap E: no reaction names the promise
`newPromise` allocates (its reaction lists are new and empty). Gap I:
`startJob` answers the head of the queue and leaves the rest. Gap D:
`finishJob` finds the running job's record, and with `[[Capability]]`
*undefined* or a fired function it only returns to a checkpoint, while with an
unfired function it settles the capability's promise with the handler's
result. The other five operations keep the Q5 post. The nine equations are
`Iff.rfl` of the definition; `postFrom_startJob` is DB-04 M2 (it observes the
queue's order), the others DB-04 M1. -/

#check (@Whatwg.Ecma262.Agent.postFrom :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body → (op : Agent.Op value reason body) → Agent.Cert op →
      Agent.Op.Answer op → Prop)

#check (@Whatwg.Ecma262.Agent.postFrom_newPromise :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.newPromise : Agent.Op value reason body))
    (cap : Promise.Capability),
    Agent.postFrom a a' Agent.Op.newPromise c cap ↔
      Agent.post a' Agent.Op.newPromise c cap ∧
        ∀ r ∈ a'.reactions.fulfill ++ a'.reactions.reject ++ a'.held,
          r.promise ≠ cap.promise)
#check (@Whatwg.Ecma262.Agent.postFrom_resolve :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (cap : Promise.Capability) (v : value)
    (c : Agent.Cert (Agent.Op.resolve cap v : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' (Agent.Op.resolve cap v) c ans ↔
      Agent.post a' (Agent.Op.resolve cap v) c ans ∧
        ∀ f ∈ a.functions, f.resolve = cap.resolve → f.alreadyResolved = false →
          Promise.Table.get a'.table cap.promise = some (Promise.State.fulfilled v))
#check (@Whatwg.Ecma262.Agent.postFrom_reject :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (cap : Promise.Capability) (r : reason)
    (c : Agent.Cert (Agent.Op.reject cap r : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' (Agent.Op.reject cap r) c ans ↔
      Agent.post a' (Agent.Op.reject cap r) c ans ∧
        ∀ f ∈ a.functions, f.reject = cap.reject → f.alreadyResolved = false →
          Promise.Table.get a'.table cap.promise = some (Promise.State.rejected r))
#check (@Whatwg.Ecma262.Agent.postFrom_perform :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool)
    (c : Agent.Cert (Agent.Op.perform promise onFulfilled onRejected derive :
      Agent.Op value reason body))
    (ans : Option (Option Promise.Capability)),
    Agent.postFrom a a' (Agent.Op.perform promise onFulfilled onRejected derive) c ans ↔
      Agent.post a' (Agent.Op.perform promise onFulfilled onRejected derive) c ans)
#check (@Whatwg.Ecma262.Agent.postFrom_markHandled :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body) (promise : Nat)
    (c : Agent.Cert (Agent.Op.markHandled promise : Agent.Op value reason body))
    (ans : Unit),
    Agent.postFrom a a' (Agent.Op.markHandled promise) c ans ↔
      Agent.post a' (Agent.Op.markHandled promise) c ans)
#check (@Whatwg.Ecma262.Agent.postFrom_startJob :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.startJob : Agent.Op value reason body))
    (ans : Option (Agent.Job value reason × Option body)),
    Agent.postFrom a a' Agent.Op.startJob c ans ↔
      Agent.post a' Agent.Op.startJob c ans ∧
        ∃ (j : Agent.Job value reason) (rest : List (Agent.Job value reason)),
          a.queue.pending = j :: rest ∧ a'.queue.pending = rest ∧
            ans.map Prod.fst = some j)
#check (@Whatwg.Ecma262.Agent.postFrom_finishJob :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (decision : Except reason value)
    (c : Agent.Cert (Agent.Op.finishJob decision : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' (Agent.Op.finishJob decision) c ans ↔
      Agent.post a' (Agent.Op.finishJob decision) c ans ∧
        ∃ (j : Agent.Job value reason) (r : Promise.Reaction body),
          a.running = some j ∧ Agent.reactionOf a j = some r ∧
          (r.capability = none →
            a' = { a with active := Jobs.Active.checkpoint, running := none }) ∧
          ∀ cap : Promise.Capability, r.capability = some cap →
            ∀ f ∈ a.functions, f.resolve = cap.resolve →
              (f.alreadyResolved = true →
                a' = { a with active := Jobs.Active.checkpoint, running := none }) ∧
              (f.alreadyResolved = false →
                (∀ v : value,
                  Promise.reactionHandlerResult r j.argument decision = Except.ok v →
                    Promise.Table.get a'.table cap.promise =
                      some (Promise.State.fulfilled v)) ∧
                (∀ e : reason,
                  Promise.reactionHandlerResult r j.argument decision = Except.error e →
                    Promise.Table.get a'.table cap.promise =
                      some (Promise.State.rejected e))))
#check (@Whatwg.Ecma262.Agent.postFrom_enterScript :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.enterScript : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' Agent.Op.enterScript c ans ↔
      Agent.post a' Agent.Op.enterScript c ans)
#check (@Whatwg.Ecma262.Agent.postFrom_leaveScript :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.leaveScript : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' Agent.Op.leaveScript c ans ↔
      Agent.post a' Agent.Op.leaveScript c ans)

/-! The stronger post implies the Q5 post, for every operation. DB-04 M1. -/
#check (@Whatwg.Ecma262.Agent.postFrom_post :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (op : Agent.Op value reason body) (c : Agent.Cert op) (ans : Agent.Op.Answer op),
    Agent.postFrom a a' op c ans → Agent.post a' op c ans)

/-! ## 5. The second adequacy judgment

`ImplementsFrom op`: from an agent `Coherent` holds of and a request the Q5
`pre` admits, the stepped agent is later in `Extends`, `Coherent` again, and
holds the answer in `postFrom`. One theorem per operation, whether or not its
post changed, and `implementsFrom` over all nine. DB-04 M2, through
`Extends`. -/

#check (@Whatwg.Ecma262.Agent.ImplementsFrom :
  ∀ {value reason body : Type}, Agent.Op value reason body → Prop)
#check (@Whatwg.Ecma262.Agent.ImplementsFrom_iff :
  ∀ {value reason body : Type} (op : Agent.Op value reason body),
    Agent.ImplementsFrom op ↔
      ∀ (a : Agent.Agent value reason body) (c : Agent.Cert op), Agent.Coherent a →
        Agent.pre a op c →
        Agent.Extends a (Agent.step a op).1 ∧ Agent.Coherent (Agent.step a op).1 ∧
          Agent.postFrom a (Agent.step a op).1 op c (Agent.step a op).2)

#check (@Whatwg.Ecma262.Agent.newPromise_implementsFrom :
  ∀ {value reason body : Type},
    Agent.ImplementsFrom (Agent.Op.newPromise : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.resolve_implementsFrom :
  ∀ {value reason body : Type} (cap : Promise.Capability) (v : value),
    Agent.ImplementsFrom (Agent.Op.resolve cap v : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.reject_implementsFrom :
  ∀ {value reason body : Type} (cap : Promise.Capability) (r : reason),
    Agent.ImplementsFrom (Agent.Op.reject cap r : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.perform_implementsFrom :
  ∀ {value reason body : Type} (promise : Nat) (onFulfilled onRejected : Option body)
    (derive : Bool),
    Agent.ImplementsFrom (Agent.Op.perform promise onFulfilled onRejected derive :
      Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.markHandled_implementsFrom :
  ∀ {value reason body : Type} (promise : Nat),
    Agent.ImplementsFrom (Agent.Op.markHandled promise : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.startJob_implementsFrom :
  ∀ {value reason body : Type},
    Agent.ImplementsFrom (Agent.Op.startJob : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.finishJob_implementsFrom :
  ∀ {value reason body : Type} (decision : Except reason value),
    Agent.ImplementsFrom (Agent.Op.finishJob decision : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.enterScript_implementsFrom :
  ∀ {value reason body : Type},
    Agent.ImplementsFrom (Agent.Op.enterScript : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.leaveScript_implementsFrom :
  ∀ {value reason body : Type},
    Agent.ImplementsFrom (Agent.Op.leaveScript : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.implementsFrom :
  ∀ {value reason body : Type} (op : Agent.Op value reason body), Agent.ImplementsFrom op)

/-! ## 6. The reaction job's two completions (gaps G and H)

`op.newpromisereactionjob` (REACTJOB, 2702885..2705591) inner steps 6 to 9.
Gap G: the model finds the capability's stored functions by the `[[Resolve]]`
identity for both completions; for a minted capability under `WF` that is the
record the `[[Reject]]` identity finds, so an abrupt result is
`Agent.reject` through the capability and a normal one `Agent.resolve`, as
inner steps 8 and 9 say. Gap H: inner step 6.a asserts that the result is not
abrupt when `[[Capability]]` is *undefined*; the model does not check it, and
an abrupt result there is dropped. That departure is the theorem
`finishJob_abrupt_dropped`. -/

#check (@Whatwg.Ecma262.Agent.callFunctions_resolve_reject :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (result : Except reason value),
    Agent.WF a → Agent.Minted a cap →
      Agent.callFunctions a
          (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve) result =
        Agent.callFunctions a
          (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject) result)
#check (@Whatwg.Ecma262.Agent.finishJob_abrupt :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
    (r : Promise.Reaction body) (cap : Promise.Capability) (e : reason),
    Agent.WF a → a.active = Jobs.Active.job s → a.running = some job →
      Agent.reactionOf a job = some r → r.capability = some cap →
      Promise.reactionHandlerResult r job.argument decision = Except.error e →
      Agent.finishJob a decision =
        { Agent.reject a cap e with active := Jobs.Active.checkpoint, running := none })
#check (@Whatwg.Ecma262.Agent.finishJob_normal :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
    (r : Promise.Reaction body) (cap : Promise.Capability) (v : value),
    a.active = Jobs.Active.job s → a.running = some job →
      Agent.reactionOf a job = some r → r.capability = some cap →
      Promise.reactionHandlerResult r job.argument decision = Except.ok v →
      Agent.finishJob a decision =
        { Agent.resolve a cap v with active := Jobs.Active.checkpoint, running := none })
#check (@Whatwg.Ecma262.Agent.finishJob_abrupt_dropped :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
    (r : Promise.Reaction body) (e : reason),
    a.active = Jobs.Active.job s → a.running = some job →
      Agent.reactionOf a job = some r → r.capability = none →
      Promise.reactionHandlerResult r job.argument decision = Except.error e →
      Agent.finishJob a decision =
        { a with active := Jobs.Active.checkpoint, running := none })

namespace WhatwgTest.Ecma262.AgentInvariantContract

/-! ## 7. Non-vacuity of the stronger posts, at agents a run reaches

Each witness is an agent `runOps` reaches from `Agent.empty`, so `Coherent`
holds of it by `Coherent.reachable`; the request's `pre` holds by `decide` or
`rfl`, the hypothesis of the post's new content holds, and the new content is
computed by `rfl`. The builder may repair a proof here; it may not change a
statement. -/

/-- The reached agents' parameters. -/
abbrev A : Type := Agent.Agent Unit Nat Nat
/-- The operations at those parameters. -/
abbrev O : Type := Agent.Op Unit Nat Nat

/-- The capability the first `newPromise` mints: promise `0`, functions `0`
and `1`. -/
def cap0 : Promise.Capability := Promise.Capability.mk 0 0 1

/-- One pending promise with its unfired functions. -/
def ops1 : List O := [Agent.Op.newPromise]
def a1 : A := (Agent.runOps Agent.empty ops1).1

example : Agent.Coherent a1 := Agent.Coherent.reachable ops1

/-- Gap A, `resolve`: the pre holds, the stored function is unfired, and the
promise ends fulfilled with the request's value. -/
example : Agent.pre a1 (Agent.Op.resolve cap0 () : O) () := by
  show ∃ f ∈ a1.functions, f.resolve = cap0.resolve ∧ f.reject = cap0.reject ∧
    f.promise = cap0.promise
  decide
example : a1.functions = [Promise.ResolvingFunctions.mk 0 0 1 false] := rfl
example :
    Promise.Table.get (Agent.step a1 (Agent.Op.resolve cap0 () : O)).1.table cap0.promise =
      some (Promise.State.fulfilled ()) := rfl

/-- Gap A, `reject`: the twin, with the reason `9`. -/
example : Agent.pre a1 (Agent.Op.reject cap0 9 : O) () := by
  show ∃ f ∈ a1.functions, f.resolve = cap0.resolve ∧ f.reject = cap0.reject ∧
    f.promise = cap0.promise
  decide
example :
    Promise.Table.get (Agent.step a1 (Agent.Op.reject cap0 9 : O)).1.table cap0.promise =
      some (Promise.State.rejected 9) := rfl

/-- The judgment delivers it: `resolve_implementsFrom` at `a1`, through the
stored record, gives the fulfilled state. -/
example :
    Promise.Table.get (Agent.step a1 (Agent.Op.resolve cap0 () : O)).1.table cap0.promise =
      some (Promise.State.fulfilled ()) :=
  ((Agent.postFrom_resolve _ _ cap0 () () _).mp
      (Agent.resolve_implementsFrom cap0 () a1 () (Agent.Coherent.reachable ops1)
        (by
          show ∃ f ∈ a1.functions, f.resolve = cap0.resolve ∧ f.reject = cap0.reject ∧
            f.promise = cap0.promise
          decide)).2.2).2
    (Promise.ResolvingFunctions.mk 0 0 1 false) (List.mem_singleton.mpr rfl) rfl rfl

/-- Gap E, `newPromise`: after one reaction pair is registered on promise `0`,
the next promise, `1`, is named by no reaction, while two reactions exist. -/
def ops2 : List O := [Agent.Op.newPromise, Agent.Op.perform 0 (some 7) none false]
def a2 : A := (Agent.runOps Agent.empty ops2).1

example : Agent.Coherent a2 := Agent.Coherent.reachable ops2
example : (a2.reactions.fulfill ++ a2.reactions.reject ++ a2.held).length = 2 := rfl
example :
    ∀ r ∈ (Agent.step a2 (Agent.Op.newPromise : O)).1.reactions.fulfill ++
        (Agent.step a2 (Agent.Op.newPromise : O)).1.reactions.reject ++
        (Agent.step a2 (Agent.Op.newPromise : O)).1.held,
      r.promise ≠ (Agent.step a2 (Agent.Op.newPromise : O)).2.promise := by
  decide

/-- Gap I, `startJob`: two reaction pairs on promise `0`, then `resolve`: two
jobs queued. `startJob` answers the head, `⟨0, .ok ()⟩`, and leaves the
rest. -/
def ops3 : List O :=
  [Agent.Op.newPromise, Agent.Op.perform 0 (some 7) none false,
    Agent.Op.perform 0 (some 8) none false, Agent.Op.resolve cap0 ()]
def a3 : A := (Agent.runOps Agent.empty ops3).1

example : Agent.Coherent a3 := Agent.Coherent.reachable ops3
example : Agent.pre a3 (Agent.Op.startJob : O) () :=
  ⟨rfl, fun h => by cases h⟩
example :
    a3.queue.pending =
      [Jobs.ReactionJob.mk 0 (Except.ok ()), Jobs.ReactionJob.mk 1 (Except.ok ())] := rfl
example :
    (Agent.step a3 (Agent.Op.startJob : O)).2.map Prod.fst =
        some (Jobs.ReactionJob.mk 0 (Except.ok ())) ∧
      (Agent.step a3 (Agent.Op.startJob : O)).1.queue.pending =
        [Jobs.ReactionJob.mk 1 (Except.ok ())] := ⟨rfl, rfl⟩

/-- Gap D, `finishJob`: a reaction with a derived capability (promise `1`,
functions `2` and `3`), its promise resolved and its job started. The
running job names its record, whose capability's function is unfired, and
`finishJob` settles promise `1` with the handler's result: fulfilled for a
normal decision, rejected for an abrupt one. -/
def ops4 : List O :=
  [Agent.Op.newPromise, Agent.Op.perform 0 (some 7) none true, Agent.Op.resolve cap0 (),
    Agent.Op.startJob]
def a4 : A := (Agent.runOps Agent.empty ops4).1

example : Agent.Coherent a4 := Agent.Coherent.reachable ops4
example : Agent.pre a4 (Agent.Op.finishJob (Except.ok ()) : O) () := ⟨0, rfl⟩
example :
    a4.running = some (Jobs.ReactionJob.mk 0 (Except.ok ())) ∧
      (Agent.reactionOf a4 (Jobs.ReactionJob.mk 0 (Except.ok ()))).bind
          Promise.Reaction.capability =
        some (Promise.Capability.mk 1 2 3) ∧
      a4.functions.find? (fun (f : Promise.ResolvingFunctions) => f.resolve == 2) =
        some (Promise.ResolvingFunctions.mk 1 2 3 false) := ⟨rfl, rfl, rfl⟩
example :
    Promise.Table.get (Agent.step a4 (Agent.Op.finishJob (Except.ok ()) : O)).1.table 1 =
        some (Promise.State.fulfilled ()) ∧
      Promise.Table.get (Agent.step a4 (Agent.Op.finishJob (Except.error 4) : O)).1.table 1 =
        some (Promise.State.rejected 4) := ⟨rfl, rfl⟩

/-- Gap G at the same agent: the abrupt decision goes through `Agent.reject`
on the derived capability. -/
example :
    Agent.finishJob a4 (Except.error 4) =
      { Agent.reject a4 (Promise.Capability.mk 1 2 3) 4 with
        active := Jobs.Active.checkpoint, running := none } := rfl

/-- Gap H: without a derived capability, an abrupt decision for a non-empty
handler settles nothing and records nothing; the agent only returns to a
checkpoint. -/
def ops5 : List O :=
  [Agent.Op.newPromise, Agent.Op.perform 0 (some 7) none false, Agent.Op.resolve cap0 (),
    Agent.Op.startJob]
def a5 : A := (Agent.runOps Agent.empty ops5).1

example :
    (Agent.reactionOf a5 (Jobs.ReactionJob.mk 0 (Except.ok ()))).bind
        Promise.Reaction.capability = none ∧
      a5.running = some (Jobs.ReactionJob.mk 0 (Except.ok ())) := ⟨rfl, rfl⟩
example :
    Agent.finishJob a5 (Except.error 4) =
      { a5 with active := Jobs.Active.checkpoint, running := none } := rfl

/-! ## 8. Counterexample witnesses: well-formed agents `Coherent` refuses

Each agent satisfies all fourteen clauses of `WF`, shown clause by clause, no
run from `Agent.empty` reaches it, and `Coherent` refuses it through the
named clause. Rows WS-PROM-CE-048 to WS-PROM-CE-054. -/

/-- No stored function's capability, for the clauses that quantify over
reactions. -/
theorem noCapability (a : A)
    (h : ∀ x ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held, x.capability = none) :
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
      ∀ cap : Promise.Capability, r.capability = some cap → Agent.Minted a cap := by
  intro r hr cap hc
  rw [h r hr] at hc
  cases hc

/-- WS-PROM-CE-048 (gap A): promise `0` is rejected with `5`, its stored
function is unfired. -/
def ceA : A :=
  { table := Promise.Table.mk [(0, Promise.Cell.mk (Promise.State.rejected 5) false)] 1
    reactions := Promise.Reactions.empty
    held := []
    queue := Jobs.Queue.empty
    functions := [Promise.ResolvingFunctions.mk 0 0 1 false]
    nextFunction := 2
    active := Jobs.Active.checkpoint
    running := none
    settlements := [(0, Except.error 5)] }

theorem ceA_wf : Agent.WF ceA :=
  { tableNodup := by decide
    tableBelow := by decide
    functionsBelow := by decide
    functionsAllocated := by decide
    resolvedSettled := by decide
    reactionsBelow := by decide
    queueBelow := by decide
    paired := rfl
    functionsNodup := by decide
    heldDistinct := by decide
    queuedKnown := by decide
    runningActive := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    capabilityStored := noCapability ceA (by decide)
    settlementsCoherent :=
      ⟨by decide, fun _ _ h => (by cases List.mem_singleton.mp h),
        fun _ _ h => (by cases List.mem_singleton.mp h; rfl)⟩ }

example : ¬ Agent.Coherent ceA := fun h =>
  absurd (h.unfiredPending _ (List.mem_singleton.mpr rfl) rfl) (by decide)

/-- The harm: `resolve` through the unfired function fires it and leaves the
promise rejected, so the Q5b post "fulfilled with the value" fails here. -/
example :
    Promise.Table.get (Agent.resolve ceA cap0 ()).table 0 =
        some (Promise.State.rejected 5) ∧
      (Agent.resolve ceA cap0 ()).functions = [Promise.ResolvingFunctions.mk 0 0 1 true] :=
  ⟨rfl, rfl⟩

/-- WS-PROM-CE-049 (gap B): promise `0` is fulfilled and its function fired,
and the trace is empty. -/
def ceB : A :=
  { table := Promise.Table.mk [(0, Promise.Cell.mk (Promise.State.fulfilled ()) false)] 1
    reactions := Promise.Reactions.empty
    held := []
    queue := Jobs.Queue.empty
    functions := [Promise.ResolvingFunctions.mk 0 0 1 true]
    nextFunction := 2
    active := Jobs.Active.checkpoint
    running := none
    settlements := [] }

theorem ceB_wf : Agent.WF ceB :=
  { tableNodup := by decide
    tableBelow := by decide
    functionsBelow := by decide
    functionsAllocated := by decide
    resolvedSettled := by decide
    reactionsBelow := by decide
    queueBelow := by decide
    paired := rfl
    functionsNodup := by decide
    heldDistinct := by decide
    queuedKnown := by decide
    runningActive := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    capabilityStored := noCapability ceB (by decide)
    settlementsCoherent :=
      ⟨List.nodup_nil, fun _ _ h => absurd h List.not_mem_nil,
        fun _ _ h => absurd h List.not_mem_nil⟩ }

example : ¬ Agent.Coherent ceB := fun h =>
  absurd (h.settledTraced.1 0 () rfl) List.not_mem_nil

/-- WS-PROM-CE-050 (gap C): promise `0` is fulfilled, its function fired and
traced, and a reaction pair still waits on it. -/
def ceC : A :=
  { table := Promise.Table.mk [(0, Promise.Cell.mk (Promise.State.fulfilled ()) false)] 1
    reactions := Promise.Reactions.mk
      [Promise.Reaction.mk 0 0 Promise.ReactionType.fulfill (some 7) none
        Promise.ReactionPhase.waiting]
      [Promise.Reaction.mk 0 0 Promise.ReactionType.reject none none
        Promise.ReactionPhase.waiting] 1
    held := []
    queue := Jobs.Queue.empty
    functions := [Promise.ResolvingFunctions.mk 0 0 1 true]
    nextFunction := 2
    active := Jobs.Active.checkpoint
    running := none
    settlements := [(0, Except.ok ())] }

theorem ceC_wf : Agent.WF ceC :=
  { tableNodup := by decide
    tableBelow := by decide
    functionsBelow := by decide
    functionsAllocated := by decide
    resolvedSettled := by decide
    reactionsBelow := by decide
    queueBelow := by decide
    paired := rfl
    functionsNodup := by decide
    heldDistinct := by decide
    queuedKnown := by decide
    runningActive := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    capabilityStored := noCapability ceC (by decide)
    settlementsCoherent :=
      ⟨by decide, fun _ _ h => (by cases List.mem_singleton.mp h; rfl),
        fun _ _ h => (by cases List.mem_singleton.mp h)⟩ }

example : ¬ Agent.Coherent ceC := fun h =>
  absurd (h.waitingPending _ (List.mem_append_left _ (List.mem_singleton.mpr rfl)) rfl)
    (by decide)

/-- The harm: the reaction waits, and no operation can queue its job, since
the only function of promise `0` has fired. -/
example :
    Promise.Reactions.waitingOn ceC.reactions 0 Promise.ReactionType.fulfill ≠ [] ∧
      (Agent.resolve ceC cap0 ()).queue.pending = [] := ⟨by decide, rfl⟩

/-- WS-PROM-CE-051 (gap D): a job runs, and no record of its identity exists. -/
def ceD : A :=
  { (Agent.empty : A) with
    active := Jobs.Active.job 0
    running := some (Jobs.ReactionJob.mk 0 (Except.ok ())) }

theorem ceD_wf : Agent.WF ceD :=
  { tableNodup := by decide
    tableBelow := by decide
    functionsBelow := by decide
    functionsAllocated := by decide
    resolvedSettled := by decide
    reactionsBelow := by decide
    queueBelow := by decide
    paired := rfl
    functionsNodup := by decide
    heldDistinct := by decide
    queuedKnown := by decide
    runningActive := ⟨fun _ h => (by cases h; rfl), fun _ _ => rfl⟩
    capabilityStored := noCapability ceD (by decide)
    settlementsCoherent :=
      ⟨List.nodup_nil, fun _ _ h => absurd h List.not_mem_nil,
        fun _ _ h => absurd h List.not_mem_nil⟩ }

example : ¬ Agent.Coherent ceD := fun h => by
  obtain ⟨r, hr, _⟩ := h.jobsTyped (Jobs.ReactionJob.mk 0 (Except.ok ())) (Or.inr rfl)
  have hn : Agent.reactionOf ceD (Jobs.ReactionJob.mk 0 (Except.ok ())) = none := rfl
  rw [hn] at hr
  cases hr

/-- The harm: `finishJob` takes the unknown-record branch and settles
nothing. -/
example :
    Agent.finishJob ceD (Except.ok ()) =
      { ceD with active := Jobs.Active.checkpoint, running := none } := rfl

/-- WS-PROM-CE-052 (gap E): a reaction pair names promise `0`, which is not
allocated; its phase is `.done`, so it waits on nothing and only
`reactionsAllocated` refuses it. -/
def ceE : A :=
  { (Agent.empty : A) with
    reactions := Promise.Reactions.mk
      [Promise.Reaction.mk 0 0 Promise.ReactionType.fulfill (some 7) none
        Promise.ReactionPhase.done]
      [Promise.Reaction.mk 0 0 Promise.ReactionType.reject none none
        Promise.ReactionPhase.done] 1 }

theorem ceE_wf : Agent.WF ceE :=
  { tableNodup := by decide
    tableBelow := by decide
    functionsBelow := by decide
    functionsAllocated := by decide
    resolvedSettled := by decide
    reactionsBelow := by decide
    queueBelow := by decide
    paired := rfl
    functionsNodup := by decide
    heldDistinct := by decide
    queuedKnown := by decide
    runningActive := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    capabilityStored := noCapability ceE (by decide)
    settlementsCoherent :=
      ⟨List.nodup_nil, fun _ _ h => absurd h List.not_mem_nil,
        fun _ _ h => absurd h List.not_mem_nil⟩ }

example : ¬ Agent.Coherent ceE := fun h =>
  absurd
    (h.reactionsAllocated _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))))
    (by decide)

/-- The harm: the next promise `newPromise` allocates is `0`, and a reaction
names it, against the new and empty reaction lists of `builtin.promise-executor`;
the Q5b post of `newPromise` fails here. -/
example :
    ∃ r ∈ (Agent.newPromise ceE).1.reactions.fulfill,
      r.promise = (Agent.newPromise ceE).2.promise := by
  decide

/-- The same stray pair, waiting: after `newPromise` and `resolve` through the
new capability, the stray reaction's job is queued for a promise nobody
reacted to. `waitingPending` refuses this agent as well. -/
def ceE' : A :=
  { (Agent.empty : A) with
    reactions := Promise.Reactions.mk
      [Promise.Reaction.mk 0 0 Promise.ReactionType.fulfill (some 7) none
        Promise.ReactionPhase.waiting]
      [Promise.Reaction.mk 0 0 Promise.ReactionType.reject none none
        Promise.ReactionPhase.waiting] 1 }

example :
    (Agent.resolve (Agent.newPromise ceE').1 (Agent.newPromise ceE').2 ()).queue.pending =
      [Jobs.ReactionJob.mk 0 (Except.ok ())] := rfl

/-- WS-PROM-CE-053 (gap F): a held record of `[[Type]]` `~fulfill~` with an
empty handler, and its job carries a rejection. -/
def ceF : A :=
  { table := Promise.Table.mk [(0, Promise.Cell.mk (Promise.State.rejected 5) true)] 1
    reactions := Promise.Reactions.mk [] [] 1
    held := [Promise.Reaction.mk 0 0 Promise.ReactionType.fulfill none none
      (Promise.ReactionPhase.queued 0)]
    queue := Jobs.Queue.mk [Jobs.ReactionJob.mk 0 (Except.error 5)]
    functions := [Promise.ResolvingFunctions.mk 0 0 1 true]
    nextFunction := 2
    active := Jobs.Active.checkpoint
    running := none
    settlements := [(0, Except.error 5)] }

theorem ceF_wf : Agent.WF ceF :=
  { tableNodup := by decide
    tableBelow := by decide
    functionsBelow := by decide
    functionsAllocated := by decide
    resolvedSettled := by decide
    reactionsBelow := by decide
    queueBelow := by decide
    paired := rfl
    functionsNodup := by decide
    heldDistinct := by decide
    queuedKnown := by decide
    runningActive := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    capabilityStored := noCapability ceF (by decide)
    settlementsCoherent :=
      ⟨by decide, fun _ _ h => (by cases List.mem_singleton.mp h),
        fun _ _ h => (by cases List.mem_singleton.mp h; rfl)⟩ }

example : ¬ Agent.Coherent ceF := fun h => by
  obtain ⟨r, hr, _, herr⟩ :=
    h.jobsTyped (Jobs.ReactionJob.mk 0 (Except.error 5)) (Or.inl (List.mem_singleton.mpr rfl))
  have hk := (herr 5 rfl).1
  have hn : Agent.reactionOf ceF (Jobs.ReactionJob.mk 0 (Except.error 5)) =
      some (Promise.Reaction.mk 0 0 Promise.ReactionType.fulfill none none
        (Promise.ReactionPhase.queued 0)) := rfl
  rw [hn] at hr
  cases hr
  cases hk

/-- The harm: the record's `[[Type]]` is `~fulfill~` and its handler is empty,
so REACTJOB inner step 4.a makes the result `NormalCompletion(argument)`; the
model's `reactionHandlerResult` reads the argument's tag instead and yields a
rejection. -/
example :
    (Agent.reactionOf ceF (Jobs.ReactionJob.mk 0 (Except.error 5))).map
        Promise.Reaction.kind =
      some Promise.ReactionType.fulfill ∧
      Promise.reactionHandlerResult
          (Promise.Reaction.mk 0 0 Promise.ReactionType.fulfill (none : Option Nat) none
            (Promise.ReactionPhase.queued 0))
          (Except.error 5 : Except Nat Unit) (Except.ok ()) =
        Except.error 5 := ⟨rfl, rfl⟩

/-- WS-PROM-CE-054 (gap F, the argument): the tag and the `[[Type]]` agree, and
the job's argument is not its promise's result: the job carries `6`, the
promise was rejected with `5`. -/
def ceF' : A :=
  { ceF with
    held := [Promise.Reaction.mk 0 0 Promise.ReactionType.reject none none
      (Promise.ReactionPhase.queued 0)]
    queue := Jobs.Queue.mk [Jobs.ReactionJob.mk 0 (Except.error 6)] }

theorem ceF'_wf : Agent.WF ceF' :=
  { tableNodup := by decide
    tableBelow := by decide
    functionsBelow := by decide
    functionsAllocated := by decide
    resolvedSettled := by decide
    reactionsBelow := by decide
    queueBelow := by decide
    paired := rfl
    functionsNodup := by decide
    heldDistinct := by decide
    queuedKnown := by decide
    runningActive := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    capabilityStored := noCapability ceF' (by decide)
    settlementsCoherent :=
      ⟨by decide, fun _ _ h => (by cases List.mem_singleton.mp h),
        fun _ _ h => (by cases List.mem_singleton.mp h; rfl)⟩ }

example : ¬ Agent.Coherent ceF' := fun h => by
  obtain ⟨r, hr, _, herr⟩ :=
    h.jobsTyped (Jobs.ReactionJob.mk 0 (Except.error 6)) (Or.inl (List.mem_singleton.mpr rfl))
  have hs := (herr 6 rfl).2
  have hn : Agent.reactionOf ceF' (Jobs.ReactionJob.mk 0 (Except.error 6)) =
      some (Promise.Reaction.mk 0 0 Promise.ReactionType.reject none none
        (Promise.ReactionPhase.queued 0)) := rfl
  rw [hn] at hr
  cases hr
  exact absurd hs (by decide)

/-! ## 9. Counterexample witnesses for the stronger post and order

WS-PROM-CE-055 (gap I): the Q5 post of `startJob` admits an answer that is not
the queue's head; `postFrom` refuses it. WS-PROM-CE-056 (gap J): `Le` admits a
later agent in which a fired one-shot marker is clear; `Extends` refuses it. -/

/-- An agent that ran the second of `a3`'s two queued jobs. -/
def ceI : A :=
  { a3 with
    queue := Jobs.Queue.mk [Jobs.ReactionJob.mk 0 (Except.ok ())]
    active := Jobs.Active.job 1
    running := some (Jobs.ReactionJob.mk 1 (Except.ok ())) }

/-- Its answer: the second job, with its record's handler. -/
def ceIAnswer : Option (Agent.Job Unit Nat × Option Nat) :=
  some (Jobs.ReactionJob.mk 1 (Except.ok ()),
    (Agent.reactionOf ceI (Jobs.ReactionJob.mk 1 (Except.ok ()))).bind
      Promise.Reaction.handler)

example : Agent.post ceI (Agent.Op.startJob : O) () ceIAnswer :=
  (Agent.post_startJob ceI () ceIAnswer).mpr
    ⟨Jobs.ReactionJob.mk 1 (Except.ok ()), rfl, rfl, rfl⟩

example : ¬ Agent.postFrom a3 ceI (Agent.Op.startJob : O) () ceIAnswer := fun h => by
  obtain ⟨_, j, rest, hq, _, hans⟩ := (Agent.postFrom_startJob a3 ceI () ceIAnswer).mp h
  have h3 : a3.queue.pending =
      [Jobs.ReactionJob.mk 0 (Except.ok ()), Jobs.ReactionJob.mk 1 (Except.ok ())] := rfl
  rw [h3] at hq
  cases hq
  cases hans

/-- An agent whose capability `cap0` has fired, and the same agent with that
marker cleared. -/
def fired : A := Agent.resolve a1 cap0 ()
def cleared : A := { fired with functions := [Promise.ResolvingFunctions.mk 0 0 1 false] }

example : fired.functions = [Promise.ResolvingFunctions.mk 0 0 1 true] := rfl

example : Agent.Le fired cleared :=
  { allocated := fun _ h => h
    settled := fun _ _ h _ => h
    handled := fun _ h => h
    tableNext := Nat.le_refl _
    reactionsNext := Nat.le_refl _
    functionCursor := Nat.le_refl _
    minted := fun f hf => by
      have e := List.mem_singleton.mp hf
      subst e
      exact ⟨Promise.ResolvingFunctions.mk 0 0 1 false, List.mem_singleton.mpr rfl, rfl, rfl,
        rfl⟩
    trace := List.prefix_refl _ }

example : ¬ Agent.Extends fired cleared := fun h =>
  absurd (h.markerKept (Promise.ResolvingFunctions.mk 0 0 1 true) (List.mem_singleton.mpr rfl)
    rfl) (by decide)

end WhatwgTest.Ecma262.AgentInvariantContract
