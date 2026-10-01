# W8 design: a generic transition kernel, one promise table, one job queue

Status: design record of the W8 seat of review lane W (rulings R-W0,
R-W1). It recommends a design and leaves the rulings to the coordinator. It
makes no Model Claim, closes no graph edge and changes no disposition. Base
commit: `97a871522ce18f792449f51300c9d93288abb398`.

Draft 1. Sections marked "pending" are filled by the measurements that
follow this commit.

Evidence labels follow `docs/research/2026-09-30-implementation-review.md`:
`[C]` measured by this seat, with its command; `[S]` read in source by this
seat; `[H]` a hypothesis not tried.

## 1. Recommendation

Provisional; amended once section 2 is measured.

Add one module, `Whatwg.Streams.Kernel`, that owns a generic labelled
derivation `Kernel.Path step : σ → List L → σ → Prop` over any one-step
relation, its laws (nil, cons, append, snoc, single, determinism, map along
a simulation), the graph of a partial function, the two-stage step
`Kernel.stage tick decide` that four of the five calculi already spell by
hand, and the fixed-external-word comparability law that today exists only
for `Semantics.Ordering`. The five per-calculus inductives stay (Route B,
R-P12's "generalize"): each calculus gains one bridge theorem
`… ↔ Kernel.Path Step …`, and its existing nil, cons and append lemmas are
re-proved as one-line corollaries. No frozen statement changes and no
authored type or definition value changes.

Order of work: W8a (kernel, bridges, the generic laws, the invariant
theorems of section 6) needs nothing from W9 and can start after the ruling.
W8b (one promise table and one job queue) waits for W9's agent record and is
a view-and-bridge slice, not a field change, unless a later ruling names the
frozen field lists it would alter.

## 2. Evidence

Pending.

## 3. Public declaration record

Pending.

## 4. Effect on frozen surfaces

Pending.

## 5. Effect on the trust gate and the strict ceiling

Pending.

## 6. Slices

Pending.

## 7. Decisions for the coordinator

Pending.

## 8. Not checked

Pending.
