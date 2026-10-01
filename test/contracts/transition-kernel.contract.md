# Transition kernel, Route B (slice W8a, ruling R-W4)

Status: **frozen red**, 2026-10-01, by the W8a breaker seat of review lane W
on branch `review/w8a-kernel-breaker`, based on `main` at `b0d35e2`.
Rulings: R-W1, R-W4 (binding brief), R-W8, R-W9, R-V5.
Design: `docs/research/2026-10-01-w8-transition-kernel-design.md` (sections
2.7, 3, 6 and appendix A).
Graphs touched: READABLE-PG-DEFAULT, WRITABLE-PG-DEFAULT,
TRANSFORM-PG-BACKPRESSURE, PIPING-PG-FORWARD-SHUTDOWN,
CONFIGURATION-PG-ORDERING.
Red declaration: `test/fixtures/trust-gate/known-red.txt`.
Batteries, all new and breaker-owned:

| Battery | `#check` | `example` | Section |
| --- | ---: | ---: | --- |
| `WhatwgTest/Streams/Kernel/PathContract.lean` | 32 | 6 | 3 |
| `WhatwgTest/Streams/Kernel/BridgeContract.lean` | 12 | 0 | 4 |
| `WhatwgTest/Streams/Readable/InvariantContract.lean` | 4 | 1 | 5.1 |
| `WhatwgTest/Streams/Writable/InvariantContract.lean` | 6 | 1 | 5.2 |
| `WhatwgTest/Streams/Semantics/InvariantContract.lean` | 6 | 2 | 5.3 |
| **total** | **60** | **10** | |

Counterexample rows `WS-KERNEL-CE-001` to `WS-KERNEL-CE-006`, with witnesses
under `WhatwgTest/Streams/Counterexamples/Kernel/` and attack shapes in
`test/counterexamples/kernel/ATTACKS.md`. No `*AxiomReport.lean` module is
written (R-W9): under the strict prefix `Whatwg.Streams` the gate's ceiling is
the axiom receipt.

The Lean batteries are the authority on names and propositions. The Lean in
this document is a reading aid copied from them.

## 1. Claim boundary

This packet freezes statements. It proves nothing, admits no declaration,
closes no graph edge, moves no coverage row and asserts no relation to any
host. Every declaration it freezes was proved in the design seat's prototype;
the few checks this seat added (a kind pin, ten body pins, two corollary
proofs, the witnesses) were proved by this seat against that prototype.
Section 10 records the status statement by statement.

What the packet does not claim:

- **Route B only.** Every per-calculus inductive stays: `Readable.Steps`,
  `Writable.Reaches`, `Transform.Reaches`, `Piping.Reaches`,
  `Semantics.Ordering.Reaches` and `Semantics.Ordering.EpisodePrefix` keep
  their kind, their constructors and their generated companions. The `abbrev`
  route (Route A) is refused by R-W4 and is not a fallback this packet admits.
- **No per-calculus exclusivity.** `Kernel.Exclusive` is asserted of the
  configuration alone (`Semantics.Ordering.exclusive`). It is false for the
  local Writable machine (`WS-KERNEL-CE-002`), so `Kernel.prefix_comparable`
  and `Kernel.normalized_unique` do not transfer to `Writable.Reaches`, and
  for Transform and Piping it is a scheduler question this packet does not
  open.
- **Not W8a:** `CellsWellFormed` (P8, CFG-CELLS), the three schedulers that
  drive one Writable step (`Transform.tick`, `Piping.tick` through
  `stepWritable`, `Semantics.Ordering.tick`), and a Readable machine that runs
  its own pull reactions (a `Kernel.stage runPullJob step` would be its
  closure, but which reactions run between which decisions is P8's global
  queue question). W8b (one promise table and one job queue as a view into
  W9's agent record) opens with its own design note and packet.
- No theorem here names an observation mask of `AGENTS.md`: the kernel laws
  hold of every one-step relation, and the bridges and invariants concern the
  local derivation closures, not the masks M1 or M2.

## 2. The role of `Whatwg.Streams.Kernel`

One new production module, `Whatwg/Streams/Kernel.lean`, namespace
`Whatwg.Streams.Kernel`, imported from `Whatwg/Streams.lean` (the
module-closure gate refuses it otherwise).

**Role.** The finite labelled derivations every Streams calculus composes
from its one-step relation, and the laws that hold of every such relation: a
generic labelled-path closure `Kernel.Path step : σ → List L → σ → Prop`, its
inversion, composition and transport laws, the graph and run faces of a
partial one-step function and their agreement, and the two-stage step
`Kernel.stage tick accept` with the exclusivity condition and the two
fixed-external-word laws that today exist only for the configuration. No
calculus is defined in the module. Each calculus keeps its own `Step` and its
own derivation inductive and states one bridge onto `Kernel.Path`.

**Specification anchor: none.** The module models no algorithm, internal slot
or IDL member of the pinned `index.bs`; it is proof infrastructure under the
relational face of `docs/ARCHITECTURE.md`. Its module docstring says "Spec
anchors: none", on the precedent of `Whatwg/Streams/Semantics/Step.lean`.

**Existing-type row.** `Kernel.Path` is a new native type. Its row names this
contract as the one that fixed its role, owner `Whatwg.Streams.Kernel`,
role "generic labelled derivation closure", spec anchor none, assurance route
"local receipt set linked to the laws edge" of the five graphs named above.
The row is the coordinator's to write at landing; this seat edits no record.

**Duplicate prevention** (design section 3.1, `[C]` there): no constant of
`Init`, of `Whatwg` or of the `effects` package has this content. Core has
`Relation.TransGen`, unlabelled; `effects` v0.8.0 has `Flow.Raw.ReachableFrom`
over block identifiers only.

**Ceiling.** The module is under the strict prefix `Whatwg.Streams` (R-V1):
every declaration in it reaches `propext` and `Quot.sound` at most, with no
exception added beside the strict list. The design measured every kernel
theorem of the prototype axiom-free except `path_graph_iff`, which uses
`propext`; section 10 records this seat's receipts.

**Kind.** `Kernel.Path` is an inductive proposition with exactly the two
constructors `nil` and `cons`; the battery pins this with an ascription of
`Kernel.Path.rec`. The kind of the six per-calculus inductives (Route B keeps
them) is not pinned by an ascription: the existing batteries ascribe only
`Semantics.Ordering.Reaches.nil`/`cons` and `EpisodePrefix.nil`/`cons` among
their constructors, and the design measured that Route A with alias theorems
passes them. Acceptance condition 7 (the fingerprint) is what refuses a
changed kind.

## 3. Declaration record: the kernel

Battery: `WhatwgTest/Streams/Kernel/PathContract.lean`, with
`open Whatwg.Streams` and `universe u v w x`. Every universe is a declared
universe variable, so a monomorphic implementation fails the ascription. Role
column after `Whatwg/AGENTS.md`: *canonical* (owns its content), *derived*
(a law), *view* (a function face of canonical content).

| # | Declaration | Role | Disposition |
| ---: | --- | --- | --- |
| 1 | `Kernel.Path` | canonical | new native type; inductive (kind pin `Kernel.Path.rec`) |
| 2 | `Kernel.Path.nil` | canonical | constructor |
| 3 | `Kernel.Path.cons` | canonical | constructor |
| 4 | `Kernel.Path.nil_iff` | derived | law |
| 5 | `Kernel.Path.cons_iff` | derived | law |
| 6 | `Kernel.Path.append` | derived | law |
| 7 | `Kernel.Path.append_iff` | derived | law |
| 8 | `Kernel.Path.single` | derived | law |
| 9 | `Kernel.Path.single_iff` | derived | law |
| 10 | `Kernel.Path.snoc` | derived | law |
| 11 | `Kernel.Path.snoc_iff` | derived | law |
| 12 | `Kernel.Path.mono` | derived | law |
| 13 | `Kernel.Path.congr` | derived | law |
| 14 | `Kernel.Path.map` | derived | law (simulation along a state map and a label map) |
| 15 | `Kernel.Path.invariant` | derived | law (invariant transport) |
| 16 | `Kernel.Path.lift` | derived | law (reflexive-transitive lift) |
| 17 | `Kernel.Deterministic` | canonical | predicate; body pinned |
| 18 | `Kernel.Path.deterministic` | derived | law |
| 19 | `Kernel.Graph` | view | body pinned |
| 20 | `Kernel.run` | view | equations pinned by 23 and 24 |
| 21 | `Kernel.graph_iff` | derived | law |
| 22 | `Kernel.graph_deterministic` | derived | law |
| 23 | `Kernel.run_nil` | derived | equation |
| 24 | `Kernel.run_cons` | derived | equation |
| 25 | `Kernel.path_graph_iff` | derived | law (relational face and function face agree) |
| 26 | `Kernel.stage` | canonical | two-stage step; both equations pinned |
| 27 | `Kernel.externalWord` | view | body pinned |
| 28 | `Kernel.Exclusive` | canonical | predicate; body pinned |
| 29 | `Kernel.prefix_comparable` | derived | law |
| 30 | `Kernel.silent_stuck` | derived | law |
| 31 | `Kernel.normalized_unique` | derived | law |

"Body pinned" means an `example` in the battery closes by `rfl` against the
body of appendix A of the design, so a definition whose type matches and
whose content is vacuous (`Kernel.Exclusive := fun _ _ => False`, say) fails.
`Kernel.run` needs no body pin because its two equations are theorems.

Exact signatures, as the battery ascribes them:

```lean
Kernel.Path : {σ : Type u} → {L : Type v} → (σ → L → σ → Prop) → σ → List L → σ → Prop
Kernel.Path.nil : ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop} (s : σ),
  Kernel.Path step s [] s
Kernel.Path.cons : ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop}
  {s mid t : σ} {d : L} {ds : List L},
  step s d mid → Kernel.Path step mid ds t → Kernel.Path step s (d :: ds) t
Kernel.Path.rec : ∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop}
  {motive : (s : σ) → (ds : List L) → (t : σ) → Kernel.Path step s ds t → Prop},
  (∀ (s : σ), motive s [] s (Kernel.Path.nil s)) →
  (∀ {s mid t : σ} {d : L} {ds : List L} (first : step s d mid)
      (rest : Kernel.Path step mid ds t),
      motive mid ds t rest → motive s (d :: ds) t (Kernel.Path.cons first rest)) →
  ∀ {s : σ} {ds : List L} {t : σ} (h : Kernel.Path step s ds t), motive s ds t h
```

In every row below, `∀ {σ : Type u} {L : Type v} {step : σ → L → σ → Prop}`
opens the statement and is not repeated.

```lean
Kernel.Path.nil_iff : ∀ {s t : σ}, Kernel.Path step s [] t ↔ s = t
Kernel.Path.cons_iff : ∀ {s t : σ} {d : L} {ds : List L},
  Kernel.Path step s (d :: ds) t ↔ ∃ mid, step s d mid ∧ Kernel.Path step mid ds t
Kernel.Path.append : ∀ {s mid t : σ} {left right : List L},
  Kernel.Path step s left mid → Kernel.Path step mid right t →
    Kernel.Path step s (left ++ right) t
Kernel.Path.append_iff : ∀ {s t : σ} {left right : List L},
  Kernel.Path step s (left ++ right) t ↔
    ∃ mid, Kernel.Path step s left mid ∧ Kernel.Path step mid right t
Kernel.Path.single : ∀ {s t : σ} {d : L}, step s d t → Kernel.Path step s [d] t
Kernel.Path.single_iff : ∀ {s t : σ} {d : L}, Kernel.Path step s [d] t ↔ step s d t
Kernel.Path.snoc : ∀ {s mid t : σ} {ds : List L} {d : L},
  Kernel.Path step s ds mid → step mid d t → Kernel.Path step s (ds ++ [d]) t
Kernel.Path.snoc_iff : ∀ {s t : σ} {ds : List L} {d : L},
  Kernel.Path step s (ds ++ [d]) t ↔ ∃ mid, Kernel.Path step s ds mid ∧ step mid d t
Kernel.Path.invariant : ∀ {P : σ → Prop},
  (∀ (s : σ) (d : L) (t : σ), P s → step s d t → P t) →
    ∀ {s t : σ} {ds : List L}, Kernel.Path step s ds t → P s → P t
Kernel.Path.lift : ∀ {R : σ → σ → Prop},
  (∀ (s : σ), R s s) → (∀ (a b c : σ), R a b → R b c → R a c) →
    (∀ (s : σ) (d : L) (t : σ), step s d t → R s t) →
      ∀ {s t : σ} {ds : List L}, Kernel.Path step s ds t → R s t
Kernel.Path.deterministic : Kernel.Deterministic step →
  ∀ {s t u : σ} {ds : List L}, Kernel.Path step s ds t → Kernel.Path step s ds u → t = u
```

`Kernel.Path.mono` and `Kernel.Path.congr` open with
`{step step' : σ → L → σ → Prop}` in place of `{step}`; `Kernel.Path.map`
opens with `{step} {τ : Type w} {M : Type x} {step' : τ → M → τ → Prop}
(f : σ → τ) (g : L → M)`:

```lean
Kernel.Path.mono : (∀ (s : σ) (d : L) (t : σ), step s d t → step' s d t) →
  ∀ {s t : σ} {ds : List L}, Kernel.Path step s ds t → Kernel.Path step' s ds t
Kernel.Path.congr : (∀ (s : σ) (d : L) (t : σ), step s d t ↔ step' s d t) →
  ∀ {s t : σ} {ds : List L}, Kernel.Path step s ds t ↔ Kernel.Path step' s ds t
Kernel.Path.map : (∀ (s : σ) (d : L) (t : σ), step s d t → step' (f s) (g d) (f t)) →
  ∀ {s t : σ} {ds : List L},
    Kernel.Path step s ds t → Kernel.Path step' (f s) (List.map g ds) (f t)
```

Determinism, graph and run, each opening with `{σ : Type u} {L : Type v}`
only:

```lean
Kernel.Deterministic : (σ → L → σ → Prop) → Prop
  -- body: ∀ (s : σ) (d : L) (t u : σ), step s d t → step s d u → t = u
Kernel.Graph : (σ → L → Option σ) → σ → L → σ → Prop
  -- body: next s d = some t
Kernel.run : (σ → L → Option σ) → σ → List L → Option σ
Kernel.graph_iff : ∀ (next : σ → L → Option σ) (s t : σ) (d : L),
  Kernel.Graph next s d t ↔ next s d = some t
Kernel.graph_deterministic : ∀ (next : σ → L → Option σ),
  Kernel.Deterministic (Kernel.Graph next)
Kernel.run_nil : ∀ (next : σ → L → Option σ) (s : σ), Kernel.run next s [] = some s
Kernel.run_cons : ∀ (next : σ → L → Option σ) (s : σ) (d : L) (ds : List L),
  Kernel.run next s (d :: ds) =
    match next s d with
    | some mid => Kernel.run next mid ds
    | none => none
Kernel.path_graph_iff : ∀ (next : σ → L → Option σ) {s t : σ} {ds : List L},
  Kernel.Path (Kernel.Graph next) s ds t ↔ Kernel.run next s ds = some t
```

The two-stage step, opening with `{σ : Type u} {D : Type v}` (and
`Kernel.externalWord` with `{D : Type u}` alone); write
`G := Kernel.Graph (Kernel.stage tick accept)` below, which the battery spells
out in full:

```lean
Kernel.stage : (σ → Option σ) → (σ → D → Option σ) → σ → Option D → Option σ
  -- body: stage tick accept s none = tick s; stage tick accept s (some d) = accept s d
Kernel.externalWord : List (Option D) → List D
  -- body: labels.filterMap id
Kernel.Exclusive : (σ → Option σ) → (σ → D → Option σ) → Prop
  -- body: ∀ (s t : σ) (d : D), tick s = some t → accept s d = none
Kernel.prefix_comparable :
  ∀ {tick : σ → Option σ} {accept : σ → D → Option σ},
    Kernel.Exclusive tick accept →
      ∀ (left right : List (Option D)) (s t u : σ),
        Kernel.Path G s left t → Kernel.Path G s right u →
          Kernel.externalWord left = Kernel.externalWord right →
            (∃ n : Nat, Kernel.Path G t (List.replicate n none) u) ∨
              ∃ n : Nat, Kernel.Path G u (List.replicate n none) t
Kernel.silent_stuck :
  ∀ {tick : σ → Option σ} {accept : σ → D → Option σ} {s t : σ} (n : Nat),
    tick s = none → Kernel.Path G s (List.replicate n none) t → t = s
Kernel.normalized_unique :
  ∀ {tick : σ → Option σ} {accept : σ → D → Option σ},
    Kernel.Exclusive tick accept →
      ∀ {s t u : σ} {left right : List (Option D)},
        Kernel.Path G s left t → Kernel.Path G s right u →
          Kernel.externalWord left = Kernel.externalWord right →
            tick t = none → tick u = none → t = u
```

The hypotheses are load-bearing: `Kernel.Path.deterministic` without
`Kernel.Deterministic` is false (`WS-KERNEL-CE-001`), `prefix_comparable`
without `Kernel.Exclusive` is false (`WS-KERNEL-CE-002`), and
`normalized_unique` without `tick t = none` and `tick u = none` is false even
under exclusivity (`WS-KERNEL-CE-003`).

## 4. Declaration record: the bridges

Battery: `WhatwgTest/Streams/Kernel/BridgeContract.lean`. Every bridge is an
adapter, owner the calculus module named, role *derived*, assurance route a
receipt on the **semantics edge** of its calculus graph.

| # | Module | Declaration | Graph |
| ---: | --- | --- | --- |
| 1 | `Readable/Step.lean` | `Readable.step_eq_graph` | READABLE-PG-DEFAULT |
| 2 | `Readable/Step.lean` | `Readable.steps_iff_path` | READABLE-PG-DEFAULT |
| 3 | `Writable/Step.lean` | `Writable.step_iff_stage` | WRITABLE-PG-DEFAULT |
| 4 | `Writable/Step.lean` | `Writable.reaches_iff_path` | WRITABLE-PG-DEFAULT |
| 5 | `Transform/Step.lean` | `Transform.step_iff_stage` | TRANSFORM-PG-BACKPRESSURE |
| 6 | `Transform/Step.lean` | `Transform.reaches_iff_path` | TRANSFORM-PG-BACKPRESSURE |
| 7 | `Piping/Step.lean` | `Piping.step_iff_stage` | PIPING-PG-FORWARD-SHUTDOWN |
| 8 | `Piping/Step.lean` | `Piping.reaches_iff_path` | PIPING-PG-FORWARD-SHUTDOWN |
| 9 | `Semantics/Step.lean` | `Semantics.Ordering.step_iff_stage` | CONFIGURATION-PG-ORDERING |
| 10 | `Semantics/Step.lean` | `Semantics.Ordering.reaches_iff_path` | CONFIGURATION-PG-ORDERING |
| 11 | `Semantics/Step.lean` | `Semantics.Ordering.episodePrefix_iff_path` | CONFIGURATION-PG-ORDERING |
| 12 | `Semantics/Runs.lean` | `Semantics.Ordering.exclusive` | CONFIGURATION-PG-ORDERING |

```lean
Readable.step_eq_graph : ∀ {α ε : Type},
  @Readable.Step α ε = Kernel.Graph (@Readable.step α ε)
Readable.steps_iff_path :
  ∀ {α ε : Type} {s t : Readable.State α ε} {ds : List (Readable.Decision α ε)},
    Readable.Steps s ds t ↔ Kernel.Path Readable.Step s ds t
Writable.step_iff_stage :
  ∀ {α ε : Type} (s : Writable.State α ε) (d : Option (Writable.Decision α ε))
    (t : Writable.State α ε),
    Writable.Step s d t ↔
      Kernel.Graph (Kernel.stage (@Writable.tick α ε) (@Writable.decide α ε)) s d t
Writable.reaches_iff_path :
  ∀ {α ε : Type} {s t : Writable.State α ε} {ds : List (Option (Writable.Decision α ε))},
    Writable.Reaches s ds t ↔ Kernel.Path Writable.Step s ds t
Semantics.Ordering.episodePrefix_iff_path :
  ∀ {α ε : Type} {s t : Config α ε} {ds : List (Option (Decision α ε))},
    EpisodePrefix s ds t ↔
      Kernel.Path (fun c d u => c.active ≠ Active.checkpoint ∧ Step c d u) s ds t
Semantics.Ordering.exclusive : ∀ {α ε : Type},
  Kernel.Exclusive (@Semantics.Ordering.tick α ε) (@Semantics.Ordering.decide α ε)
```

`Transform`, `Piping` and `Semantics.Ordering` state `step_iff_stage` and
`reaches_iff_path` exactly as Writable does, over `Transform.State α β ε`
(three type parameters), `Piping.State α ε` and `Semantics.Ordering.Config
α ε`, with each calculus's own `tick` and `decide`.

Why the four two-stage bridges are pointwise iffs and Readable's is an
equation: Readable's `Step s d t := step s d = some t` is `Kernel.Graph step`
by `rfl`. The other four `Step`s match on the label inside their own body,
and the elaborator does not identify that matcher with `Kernel.stage`'s at an
open label (`WS-KERNEL-CE-004`); `cases d <;> exact Iff.rfl` closes the
pointwise form.

`Semantics.Ordering.exclusive` is the existing
`Semantics.Ordering.tick_decide_exclusive` in the kernel's form, the same
condition, not a new one.

## 5. The invariants (additive amendments of P4, P5 and Q4)

Assurance route: the **construction edge** of READABLE-PG-DEFAULT,
WRITABLE-PG-DEFAULT and CONFIGURATION-PG-ORDERING. The predicates are views
(*view* role); every theorem is *derived*. Each invariant is inductive: no
step theorem carries a reachability hypothesis. Each closure theorem is
carried by `Kernel.Path.invariant` through the calculus's bridge, not by a
fresh induction.

### 5.1 `Readable.QueueInv` (amends `readable-default.contract.md`)

Battery `WhatwgTest/Streams/Readable/InvariantContract.lean`.

```lean
Readable.QueueInv : {α ε : Type} → Readable.State α ε → Prop
  -- body: Data.Queue.WF Readable.sizes s.queue ∧
  --       Data.Queue.SizesAdmissible Readable.sizes s.queue
Readable.step_queueInv :
  ∀ {α ε : Type} {s t : Readable.State α ε} {d : Readable.Decision α ε},
    Readable.QueueInv s → Readable.Step s d t → Readable.QueueInv t
Readable.steps_queueInv :
  ∀ {α ε : Type} {s t : Readable.State α ε} {ds : List (Readable.Decision α ε)},
    Readable.Steps s ds t → Readable.QueueInv s → Readable.QueueInv t
Readable.initial_queueInv :
  ∀ {α ε : Type} (algorithms : Readable.Algorithms) (hwm : Readable.Size),
    Readable.QueueInv (Readable.initial (α := α) (ε := ε) algorithms hwm)
```

The three queue-changing sites are `error` (`resetQueue`), `finishEnqueue`
(`enqueueValueWithSize`) and `read` (`dequeueValue`, which needs
`Data.DyadicSize.classified`, `ordered` and `exact`); every other operation
keeps the queue. `WS-KERNEL-CE-005` is the mutant that skips
`enqueueValueWithSize`.

### 5.2 `Writable.QueueInv` (amends `writable-default.contract.md`)

Battery `WhatwgTest/Streams/Writable/InvariantContract.lean`.

```lean
Writable.QueueInv : {α ε : Type} → Writable.State α ε → Prop
  -- body: Data.Queue.WF Writable.sizes s.queue ∧
  --       Data.Queue.SizesAdmissible Writable.sizes s.queue
Writable.tick_queueInv : ∀ {α ε : Type} (s t : Writable.State α ε),
  Writable.QueueInv s → Writable.tick s = some t → Writable.QueueInv t
Writable.decide_queueInv :
  ∀ {α ε : Type} (s t : Writable.State α ε) (d : Writable.Decision α ε),
    Writable.QueueInv s → Writable.decide s d = some t → Writable.QueueInv t
Writable.step_queueInv :
  ∀ {α ε : Type} {s t : Writable.State α ε} {d : Option (Writable.Decision α ε)},
    Writable.QueueInv s → Writable.Step s d t → Writable.QueueInv t
Writable.reaches_queueInv :
  ∀ {α ε : Type} {s t : Writable.State α ε} {ds : List (Option (Writable.Decision α ε))},
    Writable.Reaches s ds t → Writable.QueueInv s → Writable.QueueInv t
Writable.initial_queueInv :
  ∀ {α ε : Type} (hwm : Writable.Size) (alg : Writable.Algorithms)
    (promiseSeed errorSeed : Nat),
    Writable.QueueInv (Writable.initial (α := α) (ε := ε) hwm alg promiseSeed errorSeed)
```

The prototype splits `tick` with `fun_cases tick s` into 76 cases (and
`decide` into 16), closed by tactic alternatives in six classes: no step,
queue untouched, `invokeSink` (keeps the queue), growth by
`enqueueValueWithSize`, shrinkage by `dequeueValue`, and reset to
`Queue.empty` (`finishErroring`).

### 5.3 `Ordering.RegistrationsFresh` (amends `configuration-ordering.contract.md`)

Battery `WhatwgTest/Streams/Semantics/InvariantContract.lean`; every name in
namespace `Whatwg.Streams.Semantics.Ordering`.

```lean
registrationIds : {α ε : Type} → Config α ε → List Nat
  -- body: c.registrations.map (fun r => r.id)
RegistrationsFresh : {α ε : Type} → Config α ε → Prop
  -- body: (registrationIds c).Nodup ∧ ∀ i ∈ registrationIds c, i < c.nextObserver
step_registrationsFresh :
  ∀ {α ε : Type} {c t : Config α ε} {d : Option (Decision α ε)},
    RegistrationsFresh c → Step c d t → RegistrationsFresh t
reaches_registrationsFresh :
  ∀ {α ε : Type} {c t : Config α ε} {ds : List (Option (Decision α ε))},
    Reaches c ds t → RegistrationsFresh c → RegistrationsFresh t
initial_registrationsFresh :
  ∀ {α ε : Type} (owner : Nat) (hwm : Writable.Size) (alg : Writable.Algorithms)
    (promiseSeed errorSeed : Nat),
    RegistrationsFresh (initial (α := α) (ε := ε) owner hwm alg promiseSeed errorSeed)
reachable_registrations_nodup :
  ∀ {α ε : Type} {c : Config α ε} {owner : Nat} {hwm : Writable.Size}
    {alg : Writable.Algorithms} {promiseSeed errorSeed : Nat}
    {ds : List (Option (Decision α ε))},
    Reaches (initial (α := α) (ε := ε) owner hwm alg promiseSeed errorSeed) ds c →
      (c.registrations.map (fun r => r.id)).Nodup
```

Freshness alone (the `Nodup` clause) is not inductive; with the cursor bound
it is. `reachable_registrations_nodup` discharges the `Nodup` premise of
`notifySettled_reactions_bridge` and `notifySettled_queued_serial`
(amendment A4 of the Q4 contract) at every configuration reachable from
`initial`; its conclusion is spelled with the premise's own
`c.registrations.map` so that it applies without unfolding
`registrationIds`. The predicate is the first clause of the held P8a draft's
`SerialsWellFormed`. `WS-KERNEL-CE-006` is the mutant `register` that reuses
an identity.

## 6. Reuse modes: what becomes a corollary

R-P12's three modes, applied to the per-calculus closure lemmas. **Generalize**
(R-W4): the statement stays exactly as frozen, and the proof body is
re-derived from the kernel law named, through the calculus's bridge; no
fresh induction on a derivation remains. Every statement below is already
frozen by a P4 to Q4 battery and does not change.

| # | Calculus | File | Lemma | Re-derived from |
| ---: | --- | --- | --- | --- |
| 1 | Readable | `Readable/Step.lean` | `steps_nil_iff` | `steps_iff_path`, `Kernel.Path.nil_iff` |
| 2 | Readable | `Readable/Step.lean` | `steps_cons_iff` | `steps_iff_path`, `Kernel.Path.cons_iff` |
| 3 | Readable | `Readable/Step.lean` | `steps_append_iff` | `steps_iff_path`, `Kernel.Path.append_iff` |
| 4 | Writable | `Writable/Laws.lean` | `reaches_nil` | `reaches_iff_path`, `Kernel.Path.nil_iff` |
| 5 | Writable | `Writable/Laws.lean` | `reaches_cons` | `reaches_iff_path`, `Kernel.Path.cons_iff` |
| 6 | Writable | `Writable/Laws.lean` | `reaches_append_iff` | `reaches_iff_path`, `Kernel.Path.append_iff` |
| 7 | Transform | `Transform/Laws.lean` | `reaches_nil` | `reaches_iff_path`, `Kernel.Path.nil` |
| 8 | Transform | `Transform/Laws.lean` | `reaches_cons` | `reaches_iff_path`, `Kernel.Path.cons` |
| 9 | Transform | `Transform/Laws.lean` | `reaches_append` | `reaches_iff_path`, `Kernel.Path.append` |
| 10 | Piping | `Piping/Laws.lean` | `reaches_nil_iff` | `reaches_iff_path`, `Kernel.Path.nil_iff` |
| 11 | Piping | `Piping/Laws.lean` | `reaches_cons_iff` | `reaches_iff_path`, `Kernel.Path.cons_iff` |
| 12 | Piping | `Piping/Laws.lean` | `reaches_append_iff` | `reaches_iff_path`, `Kernel.Path.append_iff` |
| 13 | Semantics | `Semantics/Runs.lean` | `reaches_append` | `reaches_iff_path`, `Kernel.Path.append` |
| 14 | Semantics | `Semantics/Runs.lean` | `fixed_external_word_prefix_comparable` | `Kernel.prefix_comparable`, `exclusive`, `Kernel.Path.congr step_iff_stage` |
| 15 | Semantics | `Semantics/Runs.lean` | `fixed_external_word_normalized_unique` | `Kernel.normalized_unique`, `exclusive`, `Kernel.Path.congr step_iff_stage` |

Rows 7 and 8 are constructor applications today and contain no induction;
R-W4 names every calculus's nil, cons and append lemmas, so they too go
through the bridge. The configuration has no public nil or cons lemma; its
private `reaches_nil_eq` and `reaches_cons_inv` are deleted with the private
`strip`, `externalWord_nil_replicate` and `reaches_silent_normalized` of
`Semantics/Runs.lean`, whose content rows 14 and 15 now take from the kernel.
A private helper the two re-proofs need (the prototype's
`reaches_iff_stage_path`) stays private.

**Permitted, not required** (generalize where the builder touches the file
anyway; statements unchanged): `Semantics.Ordering.episodePrefix_reaches`
through `Kernel.Path.mono` and `episodePrefix_iff_path`;
`Writable.step_deterministic` and `Semantics.Ordering.step_deterministic`
through `Kernel.graph_deterministic`; `Piping.reaches_no_new_read` and
`Piping.reaches_selection_stable` through `Kernel.Path.invariant`.

**Keep:** every other declaration of the five calculi, including the six
derivation inductives, their constructors and generated companions, the five
`Step` definitions, `Semantics.Ordering.tick_decide_exclusive`, and
`Semantics.Ordering.externalWord` and `Normalized`. The configuration's
`externalWord` and the kernel's are both `labels.filterMap id`, so at the
configuration's decision type they agree by definition; that is what lets rows
14 and 15 pass their external-word hypothesis to the kernel unchanged, and no
bridge theorem between the two is frozen.

## 7. Assurance route

| Declarations | Route | Edge |
| --- | --- | --- |
| the 31 kernel declarations of section 3 | local signature and theorem receipts | the **laws** edge of each of the five calculus graphs |
| the 12 bridges of section 4 | receipt | the **semantics** edge of its own calculus graph |
| the 4 predicates and 12 theorems of section 5 | receipt | the **construction** edge of READABLE-PG-DEFAULT, WRITABLE-PG-DEFAULT, CONFIGURATION-PG-ORDERING |
| the 15 corollaries of section 6 | unchanged receipts, new proofs | the edge each already serves |

No sixth graph is created for the kernel (design decision 3, adopted by
R-W4). A compiling battery closes no edge; the coordinator closes edges from
the landing evidence.

## 8. Builder slices

Every slice is bound by R-V5's limits in every file it touches (section 9).
`fun_cases` is used in every proof W8a writes or re-proves (R-W4). Each slice
removes its batteries' entries from `known-red.txt` the moment they are green,
and adds their root imports to `WhatwgTest.lean` (R-W9: breakers do not).

| Slice | File fence | Content | Turns green |
| --- | --- | --- | --- |
| W8a.1 | `Whatwg/Streams/Kernel.lean` (new); `Whatwg/Streams.lean` (one import line) | the kernel of design appendix A | `PathContract`; witness module `Counterexamples/Kernel/Path` |
| W8a.2 | `Whatwg/Streams/{Readable,Writable,Transform,Piping,Semantics}/Step.lean` (one `import Whatwg.Streams.Kernel` and the bridges each); `Whatwg/Streams/{Writable,Transform,Piping}/Laws.lean`; `Whatwg/Streams/Semantics/Runs.lean` | the twelve bridges; the fifteen corollaries of section 6; deletion of the five private helpers | `BridgeContract` |
| W8a.3 | new `Whatwg/Streams/Readable/Invariants.lean`, `Whatwg/Streams/Writable/Invariants.lean`, `Whatwg/Streams/Semantics/Invariants.lean`; their three import lines in `Whatwg/Streams.lean` | the invariants of section 5 | the three `InvariantContract`s; witness module `Counterexamples/Kernel/Invariants` |
| W8a.4 | `Whatwg/Ecma262/Promise.lean`, `Whatwg/Streams/Writable/Laws.lean`, `Whatwg/Streams/Readable/Laws.lean`, `Whatwg/Streams/Piping/Laws.lean` | `find?` over `map`: proof bodies only (core `List.find?_map`, and one keyed-update lemma; see section 11) | none (proof-only) |
| W8a.5 | `Whatwg/Streams/Semantics/Configuration.lean` | the docstring of `notifySettled`: the owner clause holds by representation, not by `CellsWellFormed`; debt D38 is read with that sentence | none (docstring only) |

Order: W8a.1, then W8a.2, then W8a.3; W8a.4 and W8a.5 are independent.
Readable's bridge lives in `Readable/Step.lean`, where `steps_nil_iff` and
its two siblings already are. `Semantics.Ordering.exclusive` lives in
`Semantics/Runs.lean`, beside `tick_decide_exclusive`.

## 9. Limits every slice keeps (R-V5, R-W1, R-W4)

- No existing theorem statement, definition body, derived instance or
  battery changes. Additive declarations are the ones this packet freezes.
- No declaration in `Whatwg.Streams` (or `Whatwg.Ecma262`, for W8a.4)
  reaches `Classical.choice`, and no exception is added beside the strict
  list. `Whatwg/AGENTS.md` lists the causes lane V measured (`by_cases`
  without a `Decidable` instance, `simp` closing `n == n` through `BEq.rfl`,
  some `omega` shapes, `grind`); the design measured that plain `simp`
  proving `seed == seed` or `seed ∉ [seed + 1]` reaches it.
- No `grind` under `Whatwg/`. No `maxHeartbeats` or `maxRecDepth` value is
  raised. `Whatwg/Streams/Piping/Runs.lean` stays inside its current limit.
- No metaprogramming (R-V10, R-W1(d)): no `register_simp_attr`, no syntax,
  no `#eval`. `simp (config := { zetaDelta := true })` is the configuration
  shape the gate admits.
- No unused `simp` argument: `warningAsError` is on, and the prototype's
  Writable invariant proof carried unused arguments that a builder trims.
- Each corollary of section 6 derives from a kernel law, not a fresh
  induction (design section 6.3).

## 10. Validation status, statement by statement

Labels (R-W9): **prototype** — proved in the design seat's prototype, as the
design records with `[C]`; **reinstated** — this seat rebuilt the prototype
in its own worktree from the design's scratch copies and elaborated the
battery statement against it; **scratch** — proved by this seat in scratch;
**probed** — evaluated on concrete instances; **unprobed** — none of these.

**What was reinstated.** In this seat's worktree, uncommitted and removed
before the last commit: the design's `Kernel.final.lean` (appendix A; two
docstrings differ from the appendix's `Kernel.lean`) as
`Whatwg/Streams/Kernel.lean`; the design's `routeB-funcases-final.patch`,
which applies cleanly to `b0d35e2` (`git apply --check` exit 0) and adds the
bridges and re-proofs to the five `Step.lean` files, the three `Laws.lean`
files and `Semantics/Runs.lean`; and the design's three invariant prototypes
as `Whatwg/Streams/{Readable,Writable,Semantics}/Invariants.lean`, with their
`import Whatwg.Streams` replaced by `Whatwg.Streams.Readable.Laws`,
`Whatwg.Streams.Writable.Laws` and `Whatwg.Streams.Semantics.Runs` and their
`#print axioms` lines dropped; four import lines in `Whatwg/Streams.lean`.
`lake build WhatwgStreams`: 81 jobs, exit 0.

| Statements | Status | Evidence against the reinstated prototype |
| --- | --- | --- |
| the 31 kernel declarations of section 3 | prototype; reinstated | `lake env lean WhatwgTest/Streams/Kernel/PathContract.lean`: exit 0, no diagnostic |
| the kind pin `Kernel.Path.rec` and the six body pins of section 3 | reinstated (this packet's additions; not in the design) | same run |
| the 12 bridges of section 4 | prototype; reinstated | `BridgeContract.lean`: exit 0 |
| `Readable.QueueInv`, its 3 theorems and its body pin | prototype; reinstated | `Readable/InvariantContract.lean`: exit 0 |
| `Writable.QueueInv`, its 5 theorems and its body pin | prototype; reinstated | `Writable/InvariantContract.lean`: exit 0 |
| `registrationIds`, `RegistrationsFresh`, their 4 theorems and 2 body pins | prototype; reinstated | `Semantics/InvariantContract.lean`: exit 0 |
| corollaries 1 to 6 and 9 to 15 of section 6 | prototype; reinstated | the reinstated tree builds with the new proofs, every P4 to Q4 battery unchanged and green |
| corollaries 7 and 8 (`Transform.reaches_nil`, `Transform.reaches_cons` through the bridge) | scratch | this seat's scratch `Corollaries.lean`: both statements, verbatim, by `reaches_iff_path.mpr (Kernel.Path.nil s)` and `reaches_iff_path.mpr (Kernel.Path.cons first (reaches_iff_path.mp rest))`, exit 0 |
| witnesses of `WS-KERNEL-CE-001` to `004` | reinstated; the toy half of 002 is this seat's (scratch) | `lake env lean WhatwgTest/Streams/Counterexamples/Kernel/Path.lean`: exit 0 |
| witnesses of `WS-KERNEL-CE-005` and `006` | reinstated; probed (both mutants evaluated on concrete states by `decide` and `rfl`) | `.../Kernel/Invariants.lean`: exit 0 |

No statement of this packet is **unprobed**.

**Axioms.** One `#print axioms` per name in a scratch file over 75 names: the
31 kernel declarations and `Kernel.Path.rec`, the 12 bridges, the 4 predicates
and 12 invariant theorems, and the 15 corollaries of section 6. Result: 33 depend
on no axiom, 7 on `propext`, 35 on `propext` and `Quot.sound`; none reaches
`Classical.choice`, `sorryAx` or any forbidden axiom.

**Gate and kernel replay.** With the prototype in place and the five batteries
and two witness modules imported into `WhatwgTest.lean` (locally, not
committed), `lake build`: 401 jobs, exit 0, gate line "checked 233 source
files and 17339 declarations; Classical.choice is reached by 84 of 13341
declarations in Whatwg, 122 of 2401 in WhatwgTest and 176 of 1597 in
WhatwgGates; strict ceiling propext and Quot.sound over 5 module prefix(es)
with 0 exact exception(s); 0 source-token exemption(s)". The `WhatwgTest`
count of declarations reaching `Classical.choice` is 122, as on `main`: the
packet's batteries and witnesses add none. `lake env leanchecker Whatwg
WhatwgTest WhatwgGates`: exit 0 in 85 s.

## 11. Open items for the coordinator

1. **The keyed-update lemma of W8a.4.** R-W4 asks for "one keyed-update
   lemma". The update-map sites it serves are in `Whatwg/Ecma262/Promise.lean`
   (four `key` lemmas) and `Whatwg/Streams/Readable/Laws.lean` (one settle
   site), two modules, so the lemma cannot be private to one of them. A public
   lemma in `Whatwg.Ecma262.Promise` is a new exported declaration that this
   packet does not freeze and PROMISE-PG-FIRST does not record. The design's
   proposed statement (probe `KeyUpdateProbe.lean`, `propext` and
   `Quot.sound`) is

   ```lean
   theorem find?_keyUpdate {β : Type} (l : List (Nat × β)) (a i : Nat) (g : β → β) :
       List.find? (fun e => e.1 == i) (l.map (fun e => if e.1 == a then (e.1, g e.2) else e)) =
         (List.find? (fun e => e.1 == i) l).map
           (fun e => if e.1 == a then (e.1, g e.2) else e)
   ```

   A ruling decides whether it lands public (with a declaration record and an
   ascription in a later breaker packet), or private in each of the two
   modules (two copies, which R-W4's "one" does not intend).

## 12. Acceptance conditions

1. All 60 ascriptions and 10 `example`s of the five batteries elaborate with
   no token changed. A repair that turns a battery green by changing an
   ascription, an `example` or a witness is a refusal, not a landing; a builder
   who finds a frozen statement false stops and reports (R-W9).
2. Both witness modules elaborate unchanged: `Counterexamples/Kernel/Path`
   once W8a.1 lands, `Counterexamples/Kernel/Invariants` once W8a.3 lands.
3. Every ascription of the P4 to Q4 batteries elaborates unchanged. Under
   `WhatwgTest/`, the slices change no file except the seven of this packet's
   red set (which they do not edit either) and `WhatwgTest.lean`, which gains
   one import per module as it turns green.
4. The fifteen corollaries of section 6 are re-derived from the kernel laws
   named there; none keeps an induction or case analysis on a derivation. The
   five private helpers of `Semantics/Runs.lean` named in section 6 are gone.
5. The gate reports 0 strict-ceiling exceptions, and the number of `Whatwg`
   declarations reaching `Classical.choice` does not grow (84 at `b0d35e2`,
   none under a strict prefix). `lake env leanchecker Whatwg WhatwgTest
   WhatwgGates` passes.
6. Section 9 holds in every touched file. In particular
   `Whatwg/Streams/Piping/Runs.lean` elaborates inside its current limit.
7. The fingerprint against the slice base shows only added authored lines, all
   under `Whatwg.Streams.Kernel` or named in sections 4 and 5; the generated
   lines that change are those of the deleted private helpers and the `_simp`
   auxiliaries of re-proved lemmas (design section 6.3).
8. Each entry of `test/fixtures/trust-gate/known-red.txt` from this packet is
   removed the moment its module is green, and the packet's slices merge to
   `main` only when all seven are gone and the root gate passes on the slice
   branch (R-W9).

## 13. Fence

**This packet may be edited by no one but this breaker seat.** Its files: this
contract; `WhatwgTest/Streams/Kernel/PathContract.lean`,
`WhatwgTest/Streams/Kernel/BridgeContract.lean`,
`WhatwgTest/Streams/{Readable,Writable,Semantics}/InvariantContract.lean`;
`WhatwgTest/Streams/Counterexamples/Kernel/{Path,Invariants}.lean`;
`test/counterexamples/kernel/ATTACKS.md`; the `WS-KERNEL-CE` block at the end
of `test/counterexamples/REGISTER.md`; the W8a block at the end of
`test/fixtures/trust-gate/known-red.txt` (from which builders remove entries
as above); and the W8a amendment sections at the end of
`readable-default.contract.md`, `writable-default.contract.md` and
`configuration-ordering.contract.md`.

The builder's fence is section 8 and nothing else. This seat edited nothing
under `Whatwg/`, no existing battery, no graph document, neither
`WhatwgTest.lean`, `COORDINATION.md`, `PLAN.md`, any `AGENTS.md` nor
`lakefile.toml`, and no existing line of any existing file.

## 14. Freeze receipt

Frozen 2026-10-01 on branch `review/w8a-kernel-breaker`, based on `main` at
`b0d35e2`. Toolchain `leanprover/lean4:v4.33.1`. After validation every
production file was restored (`git restore Whatwg WhatwgTest.lean`, the four
prototype modules deleted); `git diff b0d35e2 -- Whatwg WhatwgTest.lean` is
empty.

**Green.** `lake build WhatwgStreams`: 77 jobs, exit 0.

**Red, in the declared modules only.**

```text
lake build
✖ [349/393] Building WhatwgTest.Streams.Counterexamples.Kernel.Invariants
✖ [350/393] Building WhatwgTest.Streams.Counterexamples.Kernel.Path
✖ [375/393] Building WhatwgTest.Streams.Kernel.BridgeContract
✖ [377/393] Building WhatwgTest.Streams.Kernel.PathContract
✖ [378/393] Building WhatwgTest.Streams.Readable.InvariantContract
✖ [380/393] Building WhatwgTest.Streams.Semantics.InvariantContract
✖ [381/393] Building WhatwgTest.Streams.Writable.InvariantContract
✖ [392/393] Building WhatwgTest
Some required targets logged failures:
- WhatwgTest.Streams.Counterexamples.Kernel.Invariants
- WhatwgTest.Streams.Counterexamples.Kernel.Path
- WhatwgTest.Streams.Kernel.BridgeContract
- WhatwgTest.Streams.Kernel.PathContract
- WhatwgTest.Streams.Readable.InvariantContract
- WhatwgTest.Streams.Semantics.InvariantContract
- WhatwgTest.Streams.Writable.InvariantContract
- WhatwgTest
error: build failed
```

The root `WhatwgTest` fails with exactly seven module-closure findings, one
per module of the red set ("… is not reachable from the WhatwgTest audit
root"), and no other gate finding: R-W9 leaves the root imports to the
builder, and the trust self-test tolerates the root while `known-red.txt`
declares any module.

**Exact diagnostics**, from `lake env lean -DmaxErrors=10000 <file>`:

| Module | Diagnostics | Kinds |
| --- | ---: | --- |
| `WhatwgTest/Streams/Kernel/PathContract.lean` | 92 | 92 `lean.unknownIdentifier` |
| `WhatwgTest/Streams/Kernel/BridgeContract.lean` | 24 | 24 `lean.unknownIdentifier` |
| `WhatwgTest/Streams/Readable/InvariantContract.lean` | 10 | 10 `lean.unknownIdentifier` |
| `WhatwgTest/Streams/Writable/InvariantContract.lean` | 16 | 16 `lean.unknownIdentifier` |
| `WhatwgTest/Streams/Semantics/InvariantContract.lean` | 15 | 15 `lean.unknownIdentifier` |
| `WhatwgTest/Streams/Counterexamples/Kernel/Path.lean` | 42 | 34 `lean.unknownIdentifier`; 6 "Expected type must not contain metavariables" and 2 "unsolved goals", each in a `by` block of a theorem whose statement names an unknown kernel constant |
| `WhatwgTest/Streams/Counterexamples/Kernel/Invariants.lean` | 10 | 9 `lean.unknownIdentifier`; 1 "unsolved goals" of the same kind |
| **total** | **209** | |

In the five batteries every diagnostic is an unknown identifier. There is no
parse, import, type-mismatch or instance-synthesis failure in any of the seven
modules. In `Counterexamples/Kernel/Invariants.lean` the two CE-005 `decide`
witnesses `ce005_reference_wf` and `ce005_mutant_breaks_wf` and the two CE-006
steps `ce006_config1_step` and `ce006_mutant_step` already elaborate against
`main`: they name no new constant.

**Gates.** `lake exe whatwg_citations`: PASS, 1281 files scanned, no
line-numbered citation into a protected authored document. The trust
self-test is recorded below.
