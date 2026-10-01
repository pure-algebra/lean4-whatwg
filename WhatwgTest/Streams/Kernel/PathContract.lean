import Whatwg.Streams
import WhatwgTest.Audit.Freeze

/-!
Breaker-owned W8a battery, part one: the generic declarations of the
transition kernel `Whatwg.Streams.Kernel`.

Contract: `test/contracts/transition-kernel.contract.md`, section 3.
Design: `docs/research/2026-10-01-w8-transition-kernel-design.md`, section
3.1 and appendix A. Ruling: R-W4.
Declared red: `test/fixtures/trust-gate/known-red.txt`.

The kernel models no algorithm of the pinned specification and carries no
specification anchor, on the precedent of `Whatwg/Streams/Semantics/Step.lean`.
Its assurance route is local receipts on the laws edge of the five calculus
graphs (READABLE-PG-DEFAULT, WRITABLE-PG-DEFAULT, TRANSFORM-PG-BACKPRESSURE,
PIPING-PG-FORWARD-SHUTDOWN, CONFIGURATION-PG-ORDERING).

Thirty-one declarations are ascribed here, one `#check` each, in the order of
section 3.1 of the design, plus one kind pin (`Kernel.Path.rec`, which fixes
`Kernel.Path` as an inductive with exactly the two constructors below) and
six `example`s that pin the bodies of the five definitions whose types alone
would admit a vacuous body. Every universe is written as a declared universe
variable, so a monomorphic implementation does not satisfy an ascription.

The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

universe u v w x

/-! ## The labelled derivation closure

`Kernel.Path step s ds t`: a finite derivation of the one-step relation `step`
from `s` to `t` whose labels, in order, are `ds`. -/

#whatwg_freeze (@Kernel.Path :
  {σ : Type u} → {L : Type v} → (σ → L → σ → Prop) → σ → List L → σ → Prop)

#whatwg_freeze (@Kernel.Path.nil :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} (s : σ),
    Kernel.Path step s [] s)

#whatwg_freeze (@Kernel.Path.cons :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s mid t : σ} {d : L}
    {ds : List L},
    step s d mid → Kernel.Path step mid ds t → Kernel.Path step s (d :: ds) t)

-- Kind pin: `Kernel.Path` is an inductive proposition with exactly the two
-- constructors above, eliminating into `Prop`. A `Kernel.Path` that is a
-- definition (an `abbrev` of some other closure, say) fails here.
#whatwg_freeze (@Kernel.Path.rec :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop}
    {motive : (s : σ) → (ds : List L) → (t : σ) → Kernel.Path step s ds t → Prop},
    (∀ (s : σ), motive s [] s (Kernel.Path.nil s)) →
    (∀ {s mid t : σ} {d : L} {ds : List L} (first : step s d mid)
        (rest : Kernel.Path step mid ds t),
        motive mid ds t rest → motive s (d :: ds) t (Kernel.Path.cons first rest)) →
    ∀ {s : σ} {ds : List L} {t : σ} (h : Kernel.Path step s ds t), motive s ds t h)

/-! ## Inversion and composition -/

#whatwg_freeze (@Kernel.Path.nil_iff :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s t : σ},
    Kernel.Path step s [] t ↔ s = t) axioms []

#whatwg_freeze (@Kernel.Path.cons_iff :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s t : σ} {d : L}
    {ds : List L},
    Kernel.Path step s (d :: ds) t ↔ ∃ mid, step s d mid ∧ Kernel.Path step mid ds t) axioms []

#whatwg_freeze (@Kernel.Path.append :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s mid t : σ}
    {left right : List L},
    Kernel.Path step s left mid → Kernel.Path step mid right t →
      Kernel.Path step s (left ++ right) t) axioms []

#whatwg_freeze (@Kernel.Path.append_iff :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s t : σ}
    {left right : List L},
    Kernel.Path step s (left ++ right) t ↔
      ∃ mid, Kernel.Path step s left mid ∧ Kernel.Path step mid right t) axioms []

#whatwg_freeze (@Kernel.Path.single :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s t : σ} {d : L},
    step s d t → Kernel.Path step s [d] t) axioms []

#whatwg_freeze (@Kernel.Path.single_iff :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s t : σ} {d : L},
    Kernel.Path step s [d] t ↔ step s d t) axioms []

#whatwg_freeze (@Kernel.Path.snoc :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s mid t : σ}
    {ds : List L} {d : L},
    Kernel.Path step s ds mid → step mid d t → Kernel.Path step s (ds ++ [d]) t) axioms []

#whatwg_freeze (@Kernel.Path.snoc_iff :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {s t : σ}
    {ds : List L} {d : L},
    Kernel.Path step s (ds ++ [d]) t ↔ ∃ mid, Kernel.Path step s ds mid ∧ step mid d t) axioms []

/-! ## Transport along relations, maps and invariants -/

#whatwg_freeze (@Kernel.Path.mono :
  ∀ {σ : Type u} {L : Type v} {step step' : σ → L → σ → Prop},
    (∀ (s : σ) (d : L) (t : σ), step s d t → step' s d t) →
      ∀ {s t : σ} {ds : List L}, Kernel.Path step s ds t → Kernel.Path step' s ds t) axioms []

#whatwg_freeze (@Kernel.Path.congr :
  ∀ {σ : Type u} {L : Type v} {step step' : σ → L → σ → Prop},
    (∀ (s : σ) (d : L) (t : σ), step s d t ↔ step' s d t) →
      ∀ {s t : σ} {ds : List L}, Kernel.Path step s ds t ↔ Kernel.Path step' s ds t) axioms []

#whatwg_freeze (@Kernel.Path.map :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {τ : Type w} {M : Type x}
    {step' : τ → M → τ → Prop} (f : σ → τ) (g : L → M),
    (∀ (s : σ) (d : L) (t : σ), step s d t → step' (f s) (g d) (f t)) →
      ∀ {s t : σ} {ds : List L},
        Kernel.Path step s ds t → Kernel.Path step' (f s) (List.map g ds) (f t)) axioms []

#whatwg_freeze (@Kernel.Path.invariant :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {P : σ → Prop},
    (∀ (s : σ) (d : L) (t : σ), P s → step s d t → P t) →
      ∀ {s t : σ} {ds : List L}, Kernel.Path step s ds t → P s → P t) axioms []

#whatwg_freeze (@Kernel.Path.lift :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} {R : σ → σ → Prop},
    (∀ (s : σ), R s s) →
      (∀ (a b c : σ), R a b → R b c → R a c) →
        (∀ (s : σ) (d : L) (t : σ), step s d t → R s t) →
          ∀ {s t : σ} {ds : List L}, Kernel.Path step s ds t → R s t) axioms []

/-! ## Determinism -/

#whatwg_freeze (@Kernel.Deterministic :
  {σ : Type u} → {L : Type v} → (σ → L → σ → Prop) → Prop)

-- Body pin: at most one successor per state and label.
example {σ : Type u} {L : Type v} (step : σ → L → σ → Prop) :
    Kernel.Deterministic step = ∀ (s : σ) (d : L) (t u : σ), step s d t → step s d u → t = u :=
  rfl

#whatwg_freeze (@Kernel.Path.deterministic :
  ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop},
    Kernel.Deterministic step →
      ∀ {s t u : σ} {ds : List L}, Kernel.Path step s ds t → Kernel.Path step s ds u → t = u) axioms []

/-! ## The graph and run faces of a partial step -/

#whatwg_freeze (@Kernel.Graph :
  {σ : Type u} → {L : Type v} → (σ → L → Option σ) → σ → L → σ → Prop)

-- Body pin: the graph of `next`.
example {σ : Type u} {L : Type v} (next : σ → L → Option σ) (s : σ) (d : L) (t : σ) :
    Kernel.Graph next s d t = (next s d = some t) :=
  rfl

#whatwg_freeze (@Kernel.run :
  {σ : Type u} → {L : Type v} → (σ → L → Option σ) → σ → List L → Option σ)

#whatwg_freeze (@Kernel.graph_iff :
  ∀ {σ : Type u} {L : Type v} (next : σ → L → Option σ) (s t : σ) (d : L),
    Kernel.Graph next s d t ↔ next s d = some t) axioms []

#whatwg_freeze (@Kernel.graph_deterministic :
  ∀ {σ : Type u} {L : Type v} (next : σ → L → Option σ),
    Kernel.Deterministic (Kernel.Graph next)) axioms []

#whatwg_freeze (@Kernel.run_nil :
  ∀ {σ : Type u} {L : Type v} (next : σ → L → Option σ) (s : σ),
    Kernel.run next s [] = some s) axioms []

#whatwg_freeze (@Kernel.run_cons :
  ∀ {σ : Type u} {L : Type v} (next : σ → L → Option σ) (s : σ) (d : L) (ds : List L),
    Kernel.run next s (d :: ds) =
      match next s d with
      | some mid => Kernel.run next mid ds
      | none => none) axioms []

#whatwg_freeze (@Kernel.path_graph_iff :
  ∀ {σ : Type u} {L : Type v} (next : σ → L → Option σ) {s t : σ} {ds : List L},
    Kernel.Path (Kernel.Graph next) s ds t ↔ Kernel.run next s ds = some t) axioms [propext]

/-! ## The two-stage step

`Kernel.stage tick accept`: the label `none` runs the deterministic stage
`tick`, the label `some d` admits decision `d` through `accept`. -/

#whatwg_freeze (@Kernel.stage :
  {σ : Type u} → {D : Type v} → (σ → Option σ) → (σ → D → Option σ) →
    σ → Option D → Option σ)

-- Body pins: the silent label runs `tick`, a decision label runs `accept`.
example {σ : Type u} {D : Type v} (tick : σ → Option σ) (accept : σ → D → Option σ)
    (s : σ) : Kernel.stage tick accept s none = tick s :=
  rfl

example {σ : Type u} {D : Type v} (tick : σ → Option σ) (accept : σ → D → Option σ)
    (s : σ) (d : D) : Kernel.stage tick accept s (some d) = accept s d :=
  rfl

-- R-W27, 2026-10-01: the universe is written `v`, the name the declaration
-- binds; the freeze command compares universe names. The statement is the
-- same up to that renaming, and it was green under `#check` with `u`.
#whatwg_freeze (@Kernel.externalWord : {D : Type v} → List (Option D) → List D)

-- Body pin: the admitted decisions in order, silent labels dropped.
example {D : Type u} (labels : List (Option D)) :
    Kernel.externalWord labels = labels.filterMap id :=
  rfl

#whatwg_freeze (@Kernel.Exclusive :
  {σ : Type u} → {D : Type v} → (σ → Option σ) → (σ → D → Option σ) → Prop)

-- Body pin: where the deterministic stage steps, no decision is admitted.
example {σ : Type u} {D : Type v} (tick : σ → Option σ) (accept : σ → D → Option σ) :
    Kernel.Exclusive tick accept = ∀ (s t : σ) (d : D), tick s = some t → accept s d = none :=
  rfl

#whatwg_freeze (@Kernel.prefix_comparable :
  ∀ {σ : Type u} {D : Type v} {tick : σ → Option σ} {accept : σ → D → Option σ},
    Kernel.Exclusive tick accept →
      ∀ (left right : List (Option D)) (s t u : σ),
        Kernel.Path (Kernel.Graph (Kernel.stage tick accept)) s left t →
          Kernel.Path (Kernel.Graph (Kernel.stage tick accept)) s right u →
            Kernel.externalWord left = Kernel.externalWord right →
              (∃ n : Nat,
                  Kernel.Path (Kernel.Graph (Kernel.stage tick accept)) t
                    (List.replicate n none) u) ∨
                ∃ n : Nat,
                  Kernel.Path (Kernel.Graph (Kernel.stage tick accept)) u
                    (List.replicate n none) t) axioms []

#whatwg_freeze (@Kernel.silent_stuck :
  ∀ {σ : Type u} {D : Type v} {tick : σ → Option σ} {accept : σ → D → Option σ}
    {s t : σ} (n : Nat),
    tick s = none →
      Kernel.Path (Kernel.Graph (Kernel.stage tick accept)) s (List.replicate n none) t →
        t = s) axioms []

#whatwg_freeze (@Kernel.normalized_unique :
  ∀ {σ : Type u} {D : Type v} {tick : σ → Option σ} {accept : σ → D → Option σ},
    Kernel.Exclusive tick accept →
      ∀ {s t u : σ} {left right : List (Option D)},
        Kernel.Path (Kernel.Graph (Kernel.stage tick accept)) s left t →
          Kernel.Path (Kernel.Graph (Kernel.stage tick accept)) s right u →
            Kernel.externalWord left = Kernel.externalWord right →
              tick t = none → tick u = none → t = u) axioms []
