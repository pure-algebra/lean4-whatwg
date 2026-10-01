import Whatwg
import Effects.Algebra.Sum

/-!
Breaker-owned Q5 battery for slice B4: the `Effects.Signature` face of the
ECMAScript agent, its canonical, lens and sum handlers, the step-fold `run`
a program denotes, the four handler–step agreement laws, and "a promise
resolved with" as a two-operation program.

Packet: `test/contracts/promise-agent-q5.contract.md`.
Graph: `PROMISE-PG-AGENT`, `docs/PROMISE-AGENT-DAG.md`.
Attacks: `test/counterexamples/promise/ATTACKS.md`, section "Q5 agent
packet", row WS-PROM-CE-047.

Every ascription names a declaration that does not exist at `b0d35e2`: this
module is red until builder slice B4 lands `Whatwg/Signatures.lean` and
`Whatwg/Signatures/Ecma262.lean`, the Lake library `WhatwgSignatures` with
its `defaultTargets` entry, and the umbrella import in `Whatwg.lean` (R-W3).
The coordinator adds `Whatwg.Signatures` to `strictCeilingPrefixes` at the B4
landing. The face imports `Effects.Algebra.Sum` and nothing else from the
`effects` package; the data model imports no `Effects` module. This battery
imports `Effects.Algebra.Sum` itself only so that its consumer-side half (the
toy signature of §4) elaborates on its own.

The face has no census row: it is an adapter, route G (targets). Masks are
DB-04's, written "DB-04 M1" and "DB-04 M2"; no Lean name here spells a mask,
and `Effects.Trace.Mask.m1`/`m2` are not used.
-/

set_option autoImplicit false

open Whatwg.Ecma262

/-! ## 1. The signature and its handlers

`signature` is an `abbrev`, as lean4-effect4's `StoreSig` is: as a `def` it
blocks `Effects.interpret_perform`'s unification. Both universes are `0`. -/

#check (@Whatwg.Signatures.Ecma262.signature : Type → Type → Type → Effects.Signature.{0, 0})

#check (@Whatwg.Signatures.Ecma262.handler :
  ∀ (value reason body : Type),
    Effects.Handler (Whatwg.Signatures.Ecma262.signature value reason body)
      (StateT (Agent.Agent value reason body) Id))

#check (@Whatwg.Signatures.Ecma262.handlerAt :
  ∀ {value reason body σ : Type}, (σ → Agent.Agent value reason body) →
    (Agent.Agent value reason body → σ → σ) →
    Effects.Handler (Whatwg.Signatures.Ecma262.signature value reason body) (StateT σ Id))

#check (@Whatwg.Signatures.Ecma262.sumHandler :
  ∀ {value reason body σ : Type} {T : Effects.Signature.{0, 0}},
    (σ → Agent.Agent value reason body) → (Agent.Agent value reason body → σ → σ) →
    Effects.Handler T (StateT σ Id) →
    Effects.Handler
      (Effects.Signature.sum (Whatwg.Signatures.Ecma262.signature value reason body) T)
      (StateT σ Id))

#check (@Whatwg.Signatures.Ecma262.run :
  ∀ {value reason body α : Type},
    Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α →
      Agent.Agent value reason body → α × Agent.Agent value reason body)

/-! `run`'s two defining equations: the step-fold, one `Agent.step` per
operation, continuing with its answer. DB-04 M2: the fold carries the agent,
whose queue and settlement trace are its order observation. -/
#check (@Whatwg.Signatures.Ecma262.run_pure :
  ∀ {value reason body α : Type} (x : α) (a : Agent.Agent value reason body),
    Whatwg.Signatures.Ecma262.run
        (Effects.Program.pure x :
          Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α) a =
      (x, a))
#check (@Whatwg.Signatures.Ecma262.run_vis :
  ∀ {value reason body α : Type} (op : Agent.Op value reason body)
    (k : Agent.Op.Answer op →
      Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α)
    (a : Agent.Agent value reason body),
    Whatwg.Signatures.Ecma262.run (Effects.Program.vis op k) a =
      Whatwg.Signatures.Ecma262.run (k (Agent.step a op).2) (Agent.step a op).1)

/-! ## 2. The handler is exactly `step`

DB-04 M2 for each: the observed state is the whole agent, queue and
settlement trace included. -/

#check (@Whatwg.Signatures.Ecma262.handler_handle :
  ∀ {value reason body : Type} (op : Agent.Op value reason body)
    (a : Agent.Agent value reason body),
    ((Whatwg.Signatures.Ecma262.handler value reason body).handle op).run a =
      ((Agent.step a op).2, (Agent.step a op).1))

#check (@Whatwg.Signatures.Ecma262.handlerAt_id :
  ∀ {value reason body : Type},
    Whatwg.Signatures.Ecma262.handlerAt
        (fun (a : Agent.Agent value reason body) => a)
        (fun (a : Agent.Agent value reason body) (_ : Agent.Agent value reason body) => a) =
      Whatwg.Signatures.Ecma262.handler value reason body)

/-! **Handler–step agreement.** Interpreting any program through the canonical
handler is the step-fold `run`; this refutes a handler that steps twice
(`WS-PROM-CE-047`). -/
#check (@Whatwg.Signatures.Ecma262.interpret_eq_run :
  ∀ {value reason body α : Type}
    (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α)
    (a : Agent.Agent value reason body),
    (Effects.interpret (Whatwg.Signatures.Ecma262.handler value reason body) p).run a =
      Whatwg.Signatures.Ecma262.run p a)

/-! **Lens agreement.** Under the view–update law the lens handler runs the
same fold on the viewed agent and writes back the agent the fold ends with.
The hypothesis is necessary (`WS-PROM-CE-047`, witness in §5). -/
#check (@Whatwg.Signatures.Ecma262.interpret_handlerAt :
  ∀ {value reason body σ α : Type} (view : σ → Agent.Agent value reason body)
    (update : Agent.Agent value reason body → σ → σ),
    (∀ (a : Agent.Agent value reason body) (s : σ), view (update a s) = a) →
    ∀ (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α)
      (s : σ),
      ((Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p).run s).1 =
          (Whatwg.Signatures.Ecma262.run p (view s)).1 ∧
        view ((Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p).run s).2 =
          (Whatwg.Signatures.Ecma262.run p (view s)).2)

#check (@Whatwg.Signatures.Ecma262.interpret_perform_step :
  ∀ {value reason body : Type} (op : Agent.Op value reason body)
    (a : Agent.Agent value reason body),
    (Effects.interpret (Whatwg.Signatures.Ecma262.handler value reason body)
        (Effects.Program.perform (S := Whatwg.Signatures.Ecma262.signature value reason body)
          op)).run a =
      ((Agent.step a op).2, (Agent.step a op).1))

#check (@Whatwg.Signatures.Ecma262.interpret_sumHandler_inl :
  ∀ {value reason body σ α : Type} {T : Effects.Signature.{0, 0}}
    (view : σ → Agent.Agent value reason body)
    (update : Agent.Agent value reason body → σ → σ) (other : Effects.Handler T (StateT σ Id))
    (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α),
    Effects.interpret (Whatwg.Signatures.Ecma262.sumHandler view update other)
        (Effects.Program.inl (T := T) p) =
      Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p)

/-! ## 3. "A promise resolved with" as a program

Web IDL `op.a-promise-resolved-with` (347948..348631), non-thenable branch:
allocate, then resolve through the stored functions. DB-04 M2. -/

#check (@Whatwg.Signatures.Ecma262.resolvedWith :
  ∀ {value reason body : Type}, value →
    Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body)
      Promise.Capability)

#check (@Whatwg.Signatures.Ecma262.run_resolvedWith :
  ∀ {value reason body : Type} (v : value) (a : Agent.Agent value reason body),
    Whatwg.Signatures.Ecma262.run (Whatwg.Signatures.Ecma262.resolvedWith (body := body) v) a =
      ((Agent.newPromise a).2,
        Agent.resolve (Agent.newPromise a).1 (Agent.newPromise a).2 v))

namespace WhatwgTest.Signatures.Ecma262Contract

/-! ## 4. The shape a consumer writes

A toy second signature, summed with the agent's into the consumer's own state
`StateT (Agent × Nat) Id`, as lean4-effect4 sums its `StoreSig` and `RSig`.
The agent lives in the first component; the lens law holds by `rfl`. -/

/-- The consumer's one operation: read the counter and bump it. -/
inductive TickOp where
  | tick

/-- The consumer's signature, an `abbrev` like the face's. -/
abbrev Tick : Effects.Signature.{0, 0} := ⟨TickOp, fun _ => Nat⟩

/-- The consumer's state. -/
abbrev World : Type := Agent.Agent Unit Nat Nat × Nat

/-- The consumer's own handler. -/
def tickHandler : Effects.Handler Tick (StateT World Id) :=
  ⟨fun _ s => (s.2, (s.1, s.2 + 1))⟩

/-- The view and update of the lens. -/
def view : World → Agent.Agent Unit Nat Nat := Prod.fst
def update : Agent.Agent Unit Nat Nat → World → World := fun a s => (a, s.2)

theorem lens : ∀ (a : Agent.Agent Unit Nat Nat) (s : World), view (update a s) = a :=
  fun _ _ => rfl

/-- The summed handler. -/
def both :
    Effects.Handler (Effects.Signature.sum (Whatwg.Signatures.Ecma262.signature Unit Nat Nat) Tick)
      (StateT World Id) :=
  Whatwg.Signatures.Ecma262.sumHandler view update tickHandler

/-- A mixed program: "a promise resolved with" on the agent side, then one tick
on the consumer side. -/
def mixed :
    Effects.Program (Effects.Signature.sum (Whatwg.Signatures.Ecma262.signature Unit Nat Nat) Tick)
      (Promise.Capability × Nat) :=
  Effects.Program.bind (Effects.Program.inl (Whatwg.Signatures.Ecma262.resolvedWith ()))
    (fun cap => Effects.Program.bind (Effects.Program.inr (Effects.Program.perform TickOp.tick))
      (fun n => Effects.Program.pure (cap, n)))

/-- The provider half of the run is the face's own `run`, written back through
the lens, and the consumer's counter moves once. -/
example :
    (Effects.interpret both mixed).run (Agent.empty, 5) =
      (((Whatwg.Signatures.Ecma262.run (Whatwg.Signatures.Ecma262.resolvedWith (body := Nat) ())
            (Agent.empty : Agent.Agent Unit Nat Nat)).1, 5),
        ((Whatwg.Signatures.Ecma262.run (Whatwg.Signatures.Ecma262.resolvedWith (body := Nat) ())
            (Agent.empty : Agent.Agent Unit Nat Nat)).2, 6)) := rfl

/-- `interpret_sumHandler_inl` at the consumer's instance. -/
example :
    Effects.interpret both
        (Effects.Program.inl (T := Tick)
          (Whatwg.Signatures.Ecma262.resolvedWith (value := Unit) (reason := Nat) (body := Nat) ())) =
      Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update)
        (Whatwg.Signatures.Ecma262.resolvedWith (value := Unit) (reason := Nat) (body := Nat) ()) :=
  Whatwg.Signatures.Ecma262.interpret_sumHandler_inl view update tickHandler _

/-- `interpret_handlerAt` at the consumer's instance. -/
example :
    view ((Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update)
        (Whatwg.Signatures.Ecma262.resolvedWith (value := Unit) (reason := Nat) (body := Nat)
          ())).run (Agent.empty, 5)).2 =
      (Whatwg.Signatures.Ecma262.run
        (Whatwg.Signatures.Ecma262.resolvedWith (value := Unit) (reason := Nat) (body := Nat) ())
        Agent.empty).2 :=
  (Whatwg.Signatures.Ecma262.interpret_handlerAt view update lens _ (Agent.empty, 5)).2

/-! ## 5. `WS-PROM-CE-047`: the lens law is necessary, and a double step is refuted -/

/-- A lens whose update drops the write. -/
def dropUpdate : Agent.Agent Unit Nat Nat → World → World := fun _ s => s

/-- One `newPromise`, as a program. -/
def allocate :
    Effects.Program (Whatwg.Signatures.Ecma262.signature Unit Nat Nat) Promise.Capability :=
  Effects.Program.perform (S := Whatwg.Signatures.Ecma262.signature Unit Nat Nat)
    Agent.Op.newPromise

/-- Without `view (update a s) = a` the conclusion of `interpret_handlerAt`
fails: the viewed agent is not the agent the fold ends with. -/
example :
    view ((Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view dropUpdate)
        allocate).run (Agent.empty, 0)).2 ≠
      (Whatwg.Signatures.Ecma262.run allocate (view (Agent.empty, 0))).2 := by
  decide

/-- A handler that steps twice. -/
def doubleHandler :
    Effects.Handler (Whatwg.Signatures.Ecma262.signature Unit Nat Nat)
      (StateT (Agent.Agent Unit Nat Nat) Id) :=
  ⟨fun op a => ((Agent.step (Agent.step a op).1 op).2, (Agent.step (Agent.step a op).1 op).1)⟩

/-- It disagrees with `run`, which `interpret_eq_run` forbids for the face's
handler. -/
example :
    ((Effects.interpret doubleHandler allocate).run Agent.empty).2 ≠
      (Whatwg.Signatures.Ecma262.run allocate Agent.empty).2 := by
  decide

end WhatwgTest.Signatures.Ecma262Contract
