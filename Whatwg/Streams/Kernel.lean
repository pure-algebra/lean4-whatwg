/-!
# Kernel.lean

Owner: the finite labelled derivations every Streams calculus composes from
its one-step relation, and the laws that hold of every such relation. No
calculus is defined here; each one keeps its own `Step` and its own
derivation inductive and states one bridge theorem onto `Kernel.Path`.

Spec anchors: none. This module models no algorithm, internal slot or IDL
member of the specification; it is proof infrastructure under the relational
face of `docs/ARCHITECTURE.md`, on the precedent of `Semantics/Step.lean`.

Opened by slice W8a.1 (ruling R-W4, Route B). Packet:
`test/contracts/transition-kernel.contract.md`. No graph of its own: the laws
are local receipts on the laws edge of READABLE-PG-DEFAULT,
WRITABLE-PG-DEFAULT, TRANSFORM-PG-BACKPRESSURE, PIPING-PG-FORWARD-SHUTDOWN
and CONFIGURATION-PG-ORDERING.

Three faces:

- `Path step`: the labelled derivations of a one-step relation, with
  inversion, composition and transport along relations, maps and invariants.
- `Graph next` and `run next`: the relational and function faces of a
  partial one-step function, which `path_graph_iff` makes agree. Fuel is not
  a parameter of anything here: `run` is total because a list is finite, not
  a fixed-fuel runner.
- `stage tick accept`: the two-stage step that Writable, Transform, Piping
  and the configuration spell by hand, `none` for the deterministic stage and
  `some d` for the admission of decision `d`. Under `Exclusive` two
  derivations that consume one external word differ by silent steps only
  (`prefix_comparable`), and agree where the deterministic stage is stuck
  (`normalized_unique`). The local Writable machine is not exclusive
  (`WS-KERNEL-CE-002`); of the five calculi only the configuration claims it.

No observation mask is named: the laws hold of every one-step relation.
-/

namespace Whatwg.Streams.Kernel

universe u v w x

section Path

variable {σ : Type u} {L : Type v}

/-- Finite labelled derivations of a one-step relation: `Path step s ds t`
derives `t` from `s` by one `step` per label of `ds`, in order. -/
inductive Path (step : σ → L → σ → Prop) : σ → List L → σ → Prop
  | nil (s : σ) : Path step s [] s
  | cons {s mid t : σ} {d : L} {ds : List L} :
      step s d mid → Path step mid ds t → Path step s (d :: ds) t

variable {step : σ → L → σ → Prop}

/-- An empty derivation identifies its endpoints. -/
theorem Path.nil_iff {s t : σ} : Path step s [] t ↔ s = t := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; exact .nil s

/-- A nonempty derivation is exactly its first step and the rest. -/
theorem Path.cons_iff {s t : σ} {d : L} {ds : List L} :
    Path step s (d :: ds) t ↔ ∃ mid, step s d mid ∧ Path step mid ds t := by
  constructor
  · intro h; cases h with | cons first rest => exact ⟨_, first, rest⟩
  · intro ⟨_, first, rest⟩; exact .cons first rest

/-- Derivations compose along the concatenation of their labels. -/
theorem Path.append {s mid t : σ} {left right : List L} :
    Path step s left mid → Path step mid right t → Path step s (left ++ right) t := by
  intro hl hr
  induction hl with
  | nil => exact hr
  | cons first _ ih => exact .cons first (ih hr)

/-- A derivation of a concatenation splits at the seam. -/
theorem Path.append_iff {s t : σ} {left right : List L} :
    Path step s (left ++ right) t ↔ ∃ mid, Path step s left mid ∧ Path step mid right t := by
  constructor
  · intro h
    induction left generalizing s with
    | nil => exact ⟨s, .nil s, h⟩
    | cons d ds ih =>
        cases h with
        | cons first rest =>
            have ⟨mid, before, after⟩ := ih rest
            exact ⟨mid, .cons first before, after⟩
  · intro ⟨_, before, after⟩
    exact before.append after

/-- One step is a one-label derivation. -/
theorem Path.single {s t : σ} {d : L} : step s d t → Path step s [d] t :=
  fun h => .cons h (.nil t)

/-- A one-label derivation is exactly one step. -/
theorem Path.single_iff {s t : σ} {d : L} : Path step s [d] t ↔ step s d t := by
  constructor
  · intro h
    cases h with
    | cons first rest => cases rest; exact first
  · exact Path.single

/-- A derivation extends by one step at its end. -/
theorem Path.snoc {s mid t : σ} {ds : List L} {d : L} :
    Path step s ds mid → step mid d t → Path step s (ds ++ [d]) t :=
  fun h last => h.append (.single last)

/-- A derivation whose labels end in `d` is exactly a derivation and one last
step labelled `d`. -/
theorem Path.snoc_iff {s t : σ} {ds : List L} {d : L} :
    Path step s (ds ++ [d]) t ↔ ∃ mid, Path step s ds mid ∧ step mid d t := by
  constructor
  · intro h
    have ⟨mid, before, after⟩ := Path.append_iff.mp h
    exact ⟨mid, before, Path.single_iff.mp after⟩
  · intro ⟨_, before, last⟩
    exact before.snoc last

/-- A derivation of a smaller relation is one of a larger relation. -/
theorem Path.mono {step' : σ → L → σ → Prop}
    (sub : ∀ s d t, step s d t → step' s d t) {s t : σ} {ds : List L} :
    Path step s ds t → Path step' s ds t := by
  intro h
  induction h with
  | nil s => exact .nil s
  | cons first _ ih => exact .cons (sub _ _ _ first) ih

/-- One-step relations that agree pointwise have the same derivations. -/
theorem Path.congr {step' : σ → L → σ → Prop}
    (same : ∀ s d t, step s d t ↔ step' s d t) {s t : σ} {ds : List L} :
    Path step s ds t ↔ Path step' s ds t :=
  ⟨Path.mono (fun s d t => (same s d t).mp), Path.mono (fun s d t => (same s d t).mpr)⟩

/-- A simulation carries derivations along a state map and a label map. -/
theorem Path.map {τ : Type w} {M : Type x} {step' : τ → M → τ → Prop}
    (f : σ → τ) (g : L → M) (sim : ∀ s d t, step s d t → step' (f s) (g d) (f t))
    {s t : σ} {ds : List L} :
    Path step s ds t → Path step' (f s) (ds.map g) (f t) := by
  intro h
  induction h with
  | nil s => exact .nil (f s)
  | cons first _ ih => exact .cons (sim _ _ _ first) ih

/-- A property every step keeps holds at the end of every derivation. -/
theorem Path.invariant {P : σ → Prop} (pres : ∀ s d t, P s → step s d t → P t)
    {s t : σ} {ds : List L} : Path step s ds t → P s → P t := by
  intro h
  induction h with
  | nil s => exact id
  | cons first _ ih => exact fun hs => ih (pres _ _ _ hs first)

/-- A reflexive, transitive relation that holds across every step holds across
every derivation. -/
theorem Path.lift {R : σ → σ → Prop} (refl : ∀ s, R s s)
    (trans : ∀ a b c, R a b → R b c → R a c) (one : ∀ s d t, step s d t → R s t)
    {s t : σ} {ds : List L} : Path step s ds t → R s t := by
  intro h
  induction h with
  | nil s => exact refl s
  | cons first _ ih => exact trans _ _ _ (one _ _ _ first) ih

/-- A one-step relation with at most one successor per state and label. -/
def Deterministic (step : σ → L → σ → Prop) : Prop :=
  ∀ s d t u, step s d t → step s d u → t = u

/-- A deterministic relation has at most one end per start and label list.
The hypothesis is load-bearing (`WS-KERNEL-CE-001`). -/
theorem Path.deterministic (det : Deterministic step) {s t u : σ} {ds : List L} :
    Path step s ds t → Path step s ds u → t = u := by
  intro ht
  induction ht with
  | nil s => intro hu; exact Path.nil_iff.mp hu
  | cons first _ ih =>
      intro hu
      cases hu with
      | cons first' rest' =>
          have := det _ _ _ _ first first'
          subst this
          exact ih rest'

end Path

section Graph

variable {σ : Type u} {L : Type v}

/-- The graph of a partial one-step function. -/
def Graph (next : σ → L → Option σ) (s : σ) (d : L) (t : σ) : Prop :=
  next s d = some t

/-- Run a finite label list through a partial one-step function. Total because
the list is finite; no fuel. -/
def run (next : σ → L → Option σ) : σ → List L → Option σ
  | s, [] => some s
  | s, d :: ds =>
      match next s d with
      | some mid => run next mid ds
      | none => none

/-- The graph relates a state and a label to the function's answer. -/
theorem graph_iff (next : σ → L → Option σ) (s t : σ) (d : L) :
    Graph next s d t ↔ next s d = some t := Iff.rfl

/-- The graph of a function is deterministic. -/
theorem graph_deterministic (next : σ → L → Option σ) : Deterministic (Graph next) := by
  intro s d t u ht hu
  exact Option.some.inj (ht.symm.trans hu)

/-- The empty label list runs to its start. -/
theorem run_nil (next : σ → L → Option σ) (s : σ) : run next s [] = some s := rfl

/-- A nonempty label list runs its first step, then the rest. -/
theorem run_cons (next : σ → L → Option σ) (s : σ) (d : L) (ds : List L) :
    run next s (d :: ds) =
      (match next s d with
       | some mid => run next mid ds
       | none => none) := rfl

/-- The relational face and the function face of a partial step agree. -/
theorem path_graph_iff (next : σ → L → Option σ) {s t : σ} {ds : List L} :
    Path (Graph next) s ds t ↔ run next s ds = some t := by
  induction ds generalizing s with
  | nil =>
      rw [Path.nil_iff, run_nil]
      exact ⟨fun h => h ▸ rfl, fun h => Option.some.inj h⟩
  | cons d ds ih =>
      rw [Path.cons_iff, run_cons]
      cases hnext : next s d with
      | none =>
          constructor
          · intro ⟨mid, first, _⟩
            have : next s d = some mid := first
            rw [hnext] at this
            exact nomatch this
          · intro h; exact nomatch h
      | some mid =>
          constructor
          · intro ⟨mid', first, rest⟩
            have : next s d = some mid' := first
            rw [hnext] at this
            cases Option.some.inj this
            exact ih.mp rest
          · intro h; exact ⟨mid, hnext, ih.mpr h⟩

end Graph

section TwoStage

variable {σ : Type u} {D : Type v}

/-- The two-stage step four calculi spell by hand: `none` is the deterministic
stage, `some d` the admission of decision `d`. -/
def stage (tick : σ → Option σ) (accept : σ → D → Option σ) : σ → Option D → Option σ
  | s, none => tick s
  | s, some d => accept s d

/-- The admitted decisions of a tape, in order, with the silent steps dropped. -/
def externalWord (labels : List (Option D)) : List D :=
  labels.filterMap id

/-- Where the deterministic stage steps, no decision is admitted. -/
def Exclusive (tick : σ → Option σ) (accept : σ → D → Option σ) : Prop :=
  ∀ s t d, tick s = some t → accept s d = none

variable {tick : σ → Option σ} {accept : σ → D → Option σ}

private theorem externalWord_none (rest : List (Option D)) :
    externalWord (none :: rest) = externalWord rest := rfl

private theorem externalWord_some (d : D) (rest : List (Option D)) :
    externalWord (some d :: rest) = d :: externalWord rest := rfl

private theorem externalWord_nil_replicate :
    ∀ (l : List (Option D)), externalWord l = [] → l = List.replicate l.length none
  | [], _ => rfl
  | none :: rest, h => by
      have hrest : externalWord rest = [] := h
      rw [List.length_cons, List.replicate_succ, ← externalWord_nil_replicate rest hrest]
  | some _ :: rest, h => by rw [externalWord_some] at h; exact nomatch h

/-- Under exclusivity, two derivations from one state that consume the same
external word differ by silent steps only. The hypothesis is load-bearing
(`WS-KERNEL-CE-002`). -/
theorem prefix_comparable (excl : Exclusive tick accept) :
    ∀ (left right : List (Option D)) (s t u : σ),
      Path (Graph (stage tick accept)) s left t →
      Path (Graph (stage tick accept)) s right u →
      externalWord left = externalWord right →
      (∃ n, Path (Graph (stage tick accept)) t (List.replicate n none) u) ∨
        (∃ n, Path (Graph (stage tick accept)) u (List.replicate n none) t) := by
  intro left
  induction left with
  | nil =>
      intro right s t u hl hr hw
      cases Path.nil_iff.mp hl
      have hrep := externalWord_nil_replicate right hw.symm
      exact Or.inl ⟨right.length, hrep ▸ hr⟩
  | cons d left' ih =>
      intro right s t u hl hr hw
      have ⟨mid, hstep, hrest⟩ := Path.cons_iff.mp hl
      cases d with
      | none =>
          have htick : tick s = some mid := hstep
          cases right with
          | nil =>
              cases Path.nil_iff.mp hr
              have hrep := externalWord_nil_replicate (none :: left') hw
              exact Or.inr ⟨(none :: left').length, hrep ▸ hl⟩
          | cons e right' =>
              have ⟨mid', hstep', hrest'⟩ := Path.cons_iff.mp hr
              cases e with
              | none =>
                  have hmid : mid' = mid :=
                    graph_deterministic (stage tick accept) _ _ _ _ hstep' hstep
                  subst hmid
                  exact ih right' _ t u hrest hrest'
                    (by rw [externalWord_none, externalWord_none] at hw; exact hw)
              | some e =>
                  have hnone := excl s mid e htick
                  have hcontra : accept s e = some mid' := hstep'
                  rw [hnone] at hcontra
                  exact nomatch hcontra
      | some d =>
          have hdec : accept s d = some mid := hstep
          cases right with
          | nil => rw [externalWord_some] at hw; exact nomatch hw
          | cons e right' =>
              have ⟨mid', hstep', hrest'⟩ := Path.cons_iff.mp hr
              cases e with
              | none =>
                  have htick : tick s = some mid' := hstep'
                  have hnone := excl s mid' d htick
                  rw [hnone] at hdec
                  exact nomatch hdec
              | some e =>
                  rw [externalWord_some, externalWord_some] at hw
                  have ⟨hde, hw'⟩ := List.cons.inj hw
                  subst hde
                  have hmid : mid' = mid :=
                    graph_deterministic (stage tick accept) _ _ _ _ hstep' hstep
                  subst hmid
                  exact ih right' _ t u hrest hrest' hw'

/-- A silent derivation from a state where the deterministic stage is stuck
stays put. -/
theorem silent_stuck {s t : σ} (n : Nat) (stuck : tick s = none) :
    Path (Graph (stage tick accept)) s (List.replicate n none) t → t = s := by
  intro h
  cases n with
  | zero => exact (Path.nil_iff.mp h).symm
  | succ m =>
      rw [List.replicate_succ] at h
      have ⟨mid, hstep, _⟩ := Path.cons_iff.mp h
      have hcontra : tick s = some mid := hstep
      rw [stuck] at hcontra
      exact nomatch hcontra

/-- Under exclusivity, two derivations that consume the same external word and
end where the deterministic stage is stuck end in the same state. Both
endpoint hypotheses are load-bearing (`WS-KERNEL-CE-003`). -/
theorem normalized_unique (excl : Exclusive tick accept) {s t u : σ}
    {left right : List (Option D)} :
    Path (Graph (stage tick accept)) s left t →
    Path (Graph (stage tick accept)) s right u →
    externalWord left = externalWord right →
    tick t = none → tick u = none → t = u := by
  intro hl hr hw ht hu
  rcases prefix_comparable excl left right s t u hl hr hw with ⟨n, h⟩ | ⟨n, h⟩
  · exact (silent_stuck n ht h).symm
  · exact silent_stuck n hu h

end TwoStage

end Whatwg.Streams.Kernel
