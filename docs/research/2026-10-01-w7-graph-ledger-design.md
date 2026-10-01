# W7 design: a Lean graph ledger with the markdown as its projection

Status: design record of the W7 seat of review lane W (ruling R-W0). It
states a recommended design, measurements and decisions for the coordinator.
It makes no Model Claim, closes no graph edge, and changes no disposition.
Base commit `97a8715`. Evidence labels follow
`docs/research/2026-09-30-implementation-review.md`: `[C]` measured by this
seat with the command given, `[S]` read in source, `[H]` a hypothesis not
tried.

DRAFT: this commit is the skeleton with the provisional recommendation.
Sections marked "pending" are filled by later commits on this branch.

## 1. Recommendation

Edge status becomes plain Lean data with no metaprogramming of its own. The
current-state tables become a projection under `generated/` checked for
drift by a new executable, `lake exe whatwg_ledger`, that loads the built
`.olean` environment at run time to resolve every theorem and module the
ledger names.

1. Types, renderer and pure checks: `WhatwgGates/Ledger/Model.lean`,
   importing nothing beyond `Init`. A graph is a record with exactly ten edge
   fields, so "ten edges, each once" is checked by the elaborator. An edge is
   `open` with at least one named remaining item, `closed` with grounds that
   are each checked or attested, or `notApplicable` with a reason.
2. Data: one module per graph under `WhatwgTest/Ledger/`, importing only the
   model. References are single-backtick `Name` literals, so the data imports
   no production module and the executable compiles none of `Whatwg`.
3. Reference checks: `WhatwgGates/Ledger/Check.lean` imports `Lean` and, in
   the executable only, imports the built environment and checks that every
   theorem ground is a theorem, every module ground is a module, and every
   cited file fact (ruling, debt, counterexample row, receipt section, gate
   name) is present. No command, no `elab`, no `run_cmd`: nothing joins the
   gate's `metaprogrammingModules` list.
4. Projection: `generated/graphs/<GRAPH-ID>.md`, one per graph, linked from
   each graph document's "Current state" section, which keeps its prose and
   loses its hand-written table. `lake exe whatwg_ledger --write` regenerates;
   `lake exe whatwg_ledger` compares bytes. Files are read at run time, so
   debt D49 does not reach this gate.
5. Rulings: a ruling bullet in `COORDINATION.md` that names a graph
   identifier must be cited by that graph's ledger, so a ruling that moves an
   edge without touching the ledger fails `lake exe whatwg_ledger`.

Order: breaker packet (model invariants and plants), builder slice 1 (model,
renderer, executable, two graphs), slice 2 (the other nine graphs and the
document links), slice 3 (the ruling cross-check). W6 is not a prerequisite.

(provisional; amended after the prototype below)

## 2. Evidence

Pending.

## 3. Public declaration record

Pending.

## 4. Effect on frozen surfaces

Pending.

## 5. Effect on the trust gate

Pending.

## 6. Slices

Pending.

## 7. Decisions for the coordinator

Pending.

## 8. Not checked

Pending.
