import Effects.Algebra.Sum
import Whatwg.Ecma262.Agent

/-!
# The `Effects.Signature` face of the ECMAScript agent

Owner: promise slice Q5 (ruling R-W3), graph `PROMISE-PG-AGENT`
(`docs/PROMISE-AGENT-DAG.md`), at the surface
`test/contracts/promise-agent-q5.contract.md` freezes (ruling R-W13). This
module is builder slice B4; its battery is
`WhatwgTest/Signatures/Ecma262Contract.lean`.

The agent record `Whatwg.Ecma262.Agent.Agent` and its one total step function
`Agent.step`, stated as an effect of the `effects` package: a program written
over `Effects.Program` performs promise operations, and a consumer runs it in
its own state beside its own effects. Every declaration here is an adapter.
The semantics is `Agent.step`, and nothing here adds to it.

## Operations and answers

`signature value reason body` is the `Effects.Signature.{0, 0}` whose
operations are the nine constructors of `Agent.Op value reason body` and whose
answer to `op` is `Agent.Op.Answer op`:

| Operation | Answer |
| --- | --- |
| `newPromise` | `Promise.Capability`, the new promise's capability |
| `resolve cap v`, `reject cap r` | `Unit` |
| `perform p onFulfilled onRejected derive` | `Option (Option Promise.Capability)`: `none` when `p` is not allocated, otherwise `some` of the derived capability, which is `none` unless `derive` is set |
| `markHandled p` | `Unit` |
| `startJob` | `Option (Agent.Job value reason × Option body)`: the started job with its handler descriptor, if a job started |
| `finishJob decision` | `Unit` |
| `enterScript`, `leaveScript` | `Unit` |

`value`, `reason` and `body` are the fulfilment values, the rejection reasons
and the handler descriptors, all in `Type`. Every argument is data and every
operation is total: a disabled one, such as a capability whose functions this
agent never stored, an empty queue, or `finishJob` with no job running, leaves
the agent unchanged and answers `()` or `none`, a live frontier rather than a
failure.

The signature is an `abbrev`: as a `def` it blocks the unification
`Effects.interpret_perform` needs, and a consumer's own signature, summed with
this one, wants the same. One operation is performed by
`Effects.Program.perform (S := signature value reason body) op`; the signature
is named because it cannot be recovered from the operation alone.

## Running a program

`run p a` folds `Agent.step` over the program `p` from the agent `a`, one step
per operation, each continuing with its answer, and ends with the program's
result and the last agent (`run_pure`, `run_vis`). `handler value reason body`
is the canonical handler into `StateT (Agent value reason body) Id`, one step
per operation (`handler_handle`), and `interpret_eq_run` says that interpreting
any program through it is `run`:

`(Effects.interpret (handler value reason body) p).run a = run p a`.

A consumer therefore proves facts about `run` from the agent's own laws (the
`Agent.step` equations of `Whatwg.Ecma262.Agent`, and the invariant and
adequacy laws of `Whatwg.Ecma262.AgentLaws`) and carries each one to the
interpretation by that rewrite. `interpret_perform_step` is the case of one
performed operation, through `Effects.interpret_perform`. `resolvedWith v` is
Web IDL "a promise resolved with" as a two-operation program, and
`run_resolvedWith` is its run.

`run` is structural over `Effects.Program`, so a closed run reduces by `rfl`
and `decide`, and it returns the plain pair. An interpretation's `.run s` has
the type `Id (α × σ)`, for which no `Decidable` equality is found, so a
consumer that decides an equation between whole interpreted runs wraps them in
`Id.run`.

## Embedding the agent in a larger state

`handlerAt view update` is the same handler into `StateT σ Id` for any state
`σ` that holds an agent: `view s` reads the agent, `update a s` writes one
back, and each operation steps `view s` and writes the stepped agent. Under the
lens law `∀ a s, view (update a s) = a`, `interpret_handlerAt` says the lens
handler answers what `run p (view s)` answers and leaves a state whose view is
the last agent of that run. The law is necessary: without it the conclusion
fails (`WS-PROM-CE-047`). At the identity lens `handlerAt` is `handler`
(`handlerAt_id`).

## Summing with another signature

`sumHandler view update other` handles `Effects.Signature.sum (signature value
reason body) T`, which `effects` also writes `signature value reason body ⊕ₛ T`,
into `StateT σ Id`: the agent's operations through `handlerAt view update` and
`T`'s through the consumer's own `other`. A provider program injected by
`Effects.Program.inl` is interpreted as through the lens handler alone
(`interpret_sumHandler_inl`). A consumer program injected by
`Effects.Program.inr` is interpreted as through the consumer's own `other`
alone, by `interpret_sumHandler_inr`, which states the equation at
`sumHandler`, where `rw` finds it.

An example, the shape of lean4-effect4's `RSig = StoreSig ⊕ₛ FiberSig`: a
consumer has a signature `Tick : Effects.Signature.{0, 0}` with one operation
`tick` answering `Nat`, keeps the state `Agent Unit Nat Nat × Nat`, and handles
`tick` by answering the counter and incrementing it. The lens is
`view := Prod.fst` and `update := fun a s => (a, s.2)`, whose law holds by
`rfl`, and `sumHandler Prod.fst (fun a s => (a, s.2)) tickHandler` handles
`signature Unit Nat Nat ⊕ₛ Tick`. The mixed program
`Effects.Program.bind (Effects.Program.inl (resolvedWith ())) (fun cap =>
Effects.Program.bind (Effects.Program.inr (Effects.Program.perform tick))
(fun n => Effects.Program.pure (cap, n)))`, interpreted from
`(Agent.empty, 5)`, answers the capability `run (resolvedWith ()) Agent.empty`
answers, paired with `5`, and leaves that run's last agent beside the counter
`6`. The battery's fourth section checks exactly this by `rfl`.

## What this face does not offer

No signature morphism and no handler transport: nothing from
`Effects.Experimental`, whose `Morphism` and `Transport` carry no contract; the
view and the update stand where a morphism would. No trace and no trace mask:
nothing from `Effects.Trace`, and no relation to `Effects.Trace.Mask` is
stated. The masks here are DB-04's, written "DB-04 M1" and "DB-04 M2", and
every law below is DB-04 M2, because what it observes is the whole agent, whose
settlement trace and job queue carry settlement order and job order. Nothing
from `Effects.Flow` or `Effects.Family`. No program-level adequacy rule over
lean4-effect4's `Protocol` (`run_adequate`): it waits until that module is in
the `effects` package (R-W3). No census row: the face is an adapter on route G
(targets) and moves no coverage state.

Layering: this module imports `Effects.Algebra.Sum`, and through it
`Effects.Algebra.Signature`, `Program`, `Handler`, `MonadLaws` and `Laws`, and
`Whatwg.Ecma262.Agent`, and nothing else. The data model imports no `Effects`
module, so a consumer that wants the agent without the effect algebra imports
`Whatwg.Ecma262.Agent` alone, from the library `WhatwgEcma262`. This module and
its root `Whatwg.Signatures` form the library `WhatwgSignatures`, the one
production library that builds the `effects` package, and this tree is held to
the strict ceiling, `propext` and `Quot.sound` (contract §10). It declares no
syntax and uses no notation of `effects`.
-/

namespace Whatwg.Signatures.Ecma262

open Whatwg.Ecma262

/-! ## 1. The signature and its handlers -/

/-- The agent's operations as an `Effects` signature: the operations are
`Agent.Op value reason body` and the answer to `op` is `Agent.Op.Answer op`.
Both universes are `0`, the shape lean4-effect4's signatures have. An `abbrev`,
as lean4-effect4's `StoreSig` is, so that `Effects.interpret_perform` unifies.
Face (adapter); no census row. -/
abbrev signature (value reason body : Type) : Effects.Signature.{0, 0} :=
  ⟨Agent.Op value reason body, Agent.Op.Answer⟩

/-- The canonical handler into the agent's own state monad: one `Agent.step`
per operation, answering the step's answer and leaving the stepped agent.
Face (adapter); no census row. -/
def handler (value reason body : Type) :
    Effects.Handler (signature value reason body) (StateT (Agent.Agent value reason body) Id) :=
  ⟨fun op a => ((Agent.step a op).2, (Agent.step a op).1)⟩

/-- The lens handler: the canonical handler at any state `σ` that holds an
agent, read by `view` and written back by `update`. Each operation steps
`view s` and writes the stepped agent into `s`. `interpret_handlerAt` relates it
to `run` under the lens law `∀ a s, view (update a s) = a`. Face (adapter); no
census row. -/
def handlerAt {value reason body σ : Type} (view : σ → Agent.Agent value reason body)
    (update : Agent.Agent value reason body → σ → σ) :
    Effects.Handler (signature value reason body) (StateT σ Id) :=
  ⟨fun op s => ((Agent.step (view s) op).2, update (Agent.step (view s) op).1 s)⟩

/-- The agent summed with a consumer's signature `T` into the consumer's state:
`Effects.Handler.sum` of the lens handler and the consumer's handler `other`,
the shape of lean4-effect4's `rHandler`. Face (adapter); no census row. -/
def sumHandler {value reason body σ : Type} {T : Effects.Signature.{0, 0}}
    (view : σ → Agent.Agent value reason body) (update : Agent.Agent value reason body → σ → σ)
    (other : Effects.Handler T (StateT σ Id)) :
    Effects.Handler (Effects.Signature.sum (signature value reason body) T) (StateT σ Id) :=
  Effects.Handler.sum (handlerAt view update) other

/-! ## 2. The step-fold a program denotes -/

/-- The step-fold: run each operation of the program by `Agent.step` and
continue with its answer; the result is the program's value and the last
agent. Structural over `Effects.Program`. Face (adapter); no census row. -/
def run {value reason body α : Type} :
    Effects.Program (signature value reason body) α → Agent.Agent value reason body →
      α × Agent.Agent value reason body
  | .pure x, a => (x, a)
  | .vis op k, a => run (k (Agent.step a op).2) (Agent.step a op).1

/-- A finished program leaves the agent as it is. Defining equation of `run`;
DB-04 M2, since the fold carries the whole agent. -/
theorem run_pure :
    ∀ {value reason body α : Type} (x : α) (a : Agent.Agent value reason body),
      Whatwg.Signatures.Ecma262.run
          (Effects.Program.pure x :
            Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α) a =
        (x, a) := by
  intros; rfl

/-- An operation is one `Agent.step`, and the program continues with its
answer from the stepped agent. Defining equation of `run`; DB-04 M2, since the
fold carries the whole agent. -/
theorem run_vis :
    ∀ {value reason body α : Type} (op : Agent.Op value reason body)
      (k : Agent.Op.Answer op →
        Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α)
      (a : Agent.Agent value reason body),
      Whatwg.Signatures.Ecma262.run (Effects.Program.vis op k) a =
        Whatwg.Signatures.Ecma262.run (k (Agent.step a op).2) (Agent.step a op).1 := by
  intros; rfl

/-! ## 3. The handlers agree with the step

Every law here is DB-04 M2: the observed state is the whole agent, settlement
trace and job queue included. -/

/-- The canonical handler's action at one operation is one `Agent.step`,
answer first. Face law; DB-04 M2. -/
theorem handler_handle :
    ∀ {value reason body : Type} (op : Agent.Op value reason body)
      (a : Agent.Agent value reason body),
      ((Whatwg.Signatures.Ecma262.handler value reason body).handle op).run a =
        ((Agent.step a op).2, (Agent.step a op).1) := by
  intros; rfl

/-- At the identity lens the lens handler is the canonical one. Face law;
DB-04 M2. -/
theorem handlerAt_id :
    ∀ {value reason body : Type},
      Whatwg.Signatures.Ecma262.handlerAt
          (fun (a : Agent.Agent value reason body) => a)
          (fun (a : Agent.Agent value reason body) (_ : Agent.Agent value reason body) => a) =
        Whatwg.Signatures.Ecma262.handler value reason body := by
  intros; rfl

/-- **Handler–step agreement.** Interpreting any program through the canonical
handler is the step-fold `run`, so every observation of the agent agrees, its
table, reactions, queue and settlement trace included. A handler that stepped
twice would fail it (`WS-PROM-CE-047`). Face law; DB-04 M2. -/
theorem interpret_eq_run :
    ∀ {value reason body α : Type}
      (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α)
      (a : Agent.Agent value reason body),
      (Effects.interpret (Whatwg.Signatures.Ecma262.handler value reason body) p).run a =
        Whatwg.Signatures.Ecma262.run p a := by
  intro value reason body α p
  induction p with
  | pure x => intro a; rfl
  | vis op k ih => intro a; exact ih (Agent.step a op).2 (Agent.step a op).1

/-- **Lens agreement.** Under the lens law, the lens handler answers what the
step-fold on the viewed agent answers, and the state it leaves views as the
fold's last agent. The hypothesis is necessary (`WS-PROM-CE-047`). Face law;
DB-04 M2. -/
theorem interpret_handlerAt :
    ∀ {value reason body σ α : Type} (view : σ → Agent.Agent value reason body)
      (update : Agent.Agent value reason body → σ → σ),
      (∀ (a : Agent.Agent value reason body) (s : σ), view (update a s) = a) →
      ∀ (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α)
        (s : σ),
        ((Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p).run s).1 =
            (Whatwg.Signatures.Ecma262.run p (view s)).1 ∧
          view ((Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p).run s).2 =
            (Whatwg.Signatures.Ecma262.run p (view s)).2 := by
  intro value reason body σ α view update law p
  induction p with
  | pure x => intro s; exact ⟨rfl, rfl⟩
  | vis op k ih =>
      intro s
      have h := ih (Agent.step (view s) op).2 (update (Agent.step (view s) op).1 s)
      rw [law] at h
      exact h

/-- One performed operation, interpreted through the canonical handler, is one
`Agent.step`, by the `effects` law `Effects.interpret_perform`. Face law; DB-04
M2. -/
theorem interpret_perform_step :
    ∀ {value reason body : Type} (op : Agent.Op value reason body)
      (a : Agent.Agent value reason body),
      (Effects.interpret (Whatwg.Signatures.Ecma262.handler value reason body)
          (Effects.Program.perform (S := Whatwg.Signatures.Ecma262.signature value reason body)
            op)).run a =
        ((Agent.step a op).2, (Agent.step a op).1) := by
  intro value reason body op a
  rw [Effects.interpret_perform]
  rfl

/-- A provider program injected into the sum is interpreted by the lens
handler alone, by the `effects` law `Effects.interpret_inl`. Face law; DB-04
M2. -/
theorem interpret_sumHandler_inl :
    ∀ {value reason body σ α : Type} {T : Effects.Signature.{0, 0}}
      (view : σ → Agent.Agent value reason body)
      (update : Agent.Agent value reason body → σ → σ) (other : Effects.Handler T (StateT σ Id))
      (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α),
      Effects.interpret (Whatwg.Signatures.Ecma262.sumHandler view update other)
          (Effects.Program.inl (T := T) p) =
        Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p := by
  intro value reason body σ α T view update other p
  exact Effects.interpret_inl (handlerAt view update) other p

/-- A consumer program injected into the sum is interpreted by the consumer's
own handler alone, by the `effects` law `Effects.interpret_inr`: the agent's
lens handler takes no step, so no lens law is needed. The mirror of
`interpret_sumHandler_inl`, stated at `sumHandler` so that `rw` finds it. Face
law; DB-04 M2. -/
theorem interpret_sumHandler_inr :
    ∀ {value reason body σ α : Type} {T : Effects.Signature.{0, 0}}
      (view : σ → Agent.Agent value reason body)
      (update : Agent.Agent value reason body → σ → σ) (other : Effects.Handler T (StateT σ Id))
      (p : Effects.Program T α),
      Effects.interpret (Whatwg.Signatures.Ecma262.sumHandler view update other)
          (Effects.Program.inr (S := Whatwg.Signatures.Ecma262.signature value reason body) p) =
        Effects.interpret other p := by
  intro value reason body σ α T view update other p
  exact Effects.interpret_inr (handlerAt view update) other p

/-! ## 4. "A promise resolved with" as a program -/

/-- Web IDL `op.a-promise-resolved-with` (RESOLVEDW, 347948..348631, digest
`a5b86f19962066ef9844df3f2ee2494cb78c74bae6cf6690cc8ee1b6e0b60015`), steps 3 to
5 on the non-thenable branch, as a program: perform `newPromise`, perform
`resolve` through the capability it answers, and return the capability. It is
the tree of `perform newPromise` bound to `fun cap => perform (resolve cap v)`
bound to `fun _ => pure cap`, written in normal form. The step-level twin is
`Whatwg.WebIdl.Agent.resolvedWith`. Face program (adapter). -/
def resolvedWith {value reason body : Type} (v : value) :
    Effects.Program (signature value reason body) Promise.Capability :=
  .vis Agent.Op.newPromise (fun cap =>
    .vis (Agent.Op.resolve cap v) (fun _ => .pure cap))

/-- The run of "a promise resolved with" is the two steps: the capability
`newPromise` answers, and the agent after resolving through it. Face law
(`op.a-promise-resolved-with`); DB-04 M2. -/
theorem run_resolvedWith :
    ∀ {value reason body : Type} (v : value) (a : Agent.Agent value reason body),
      Whatwg.Signatures.Ecma262.run (Whatwg.Signatures.Ecma262.resolvedWith (body := body) v) a =
        ((Agent.newPromise a).2,
          Agent.resolve (Agent.newPromise a).1 (Agent.newPromise a).2 v) := by
  intros; rfl

end Whatwg.Signatures.Ecma262
