# W10 design: retarget P11 and P12; one shared gate package

Status: DRAFT, W10 design seat of review lane W, 2026-10-01, branch
`review/w10-retarget-design` from `97a8715`. Research record under rulings
R-W0 and R-W1(f). It makes no Model Claim, closes no graph edge, changes no
disposition, and edits no plan, router, contract or code. The retarget is
proposed text for `PLAN.md`; the shared gate package is a plan in the manner
of `docs/HASH-PACKAGE-PLAN.md`. Creating a repository or changing another one
is the operator's decision.

Evidence labels follow `docs/research/2026-09-30-implementation-review.md`:
`[C]` measured or read by this seat, with the command; `[S]` read in source
by a read-only helper seat of this seat and not re-read here; `[H]` a
hypothesis not tried.

## 1. Recommendation

PROVISIONAL (skeleton commit; sections 2 to 8 are being filled).

Part A. P11 consumes lean4-typescript's syntax and renderer and builds here
only what it owns: the closed combinator alphabet as first-order data, a
lowering to the host's own WHATWG Streams API, and a host harness. P12 drops
the Effect Channel embedding, whose target does not exist, and becomes an
`Effects.Signature` face of the Streams calculi built in this repository on
the `effects` package, beside the Node legacy-stream bridge. Both rows lose
the claims no pinned artifact can carry today (a typing proof against a
TypeScript semantics; a Channel embedding).

Part B. The structural repair of debt D56 is a gate executable over the
built `.olean` files. The prototype measured here imports the audit root
with `Lean.importModules (loadExts := false)`, so no audited initializer,
parser or elaborator runs; it reproduces the in-tree gate's summary counts
exactly (16,723 declarations; 84, 122 and 176 reaching `Classical.choice`)
in 2.4 s, its own axiom traversal agrees with `Lean.collectAxioms` on every
one of the 16,723 declarations, and the registrations and the final token
table rebuild from raw module entries identical to the loaded ones. The first
step is in this repository alone: `whatwg_trustgate`, an executable with its
own contract addendum, run in CI after `lake build`, sharing one library with
the in-tree command. The shared package follows on the hash precedent.

Order: (1) P11/P12 retarget text ruled; (2) the executable gate (breaker
addendum V2d, builder, review); (3) the gate logic factored into a library
with per-repository data in a config module; (4) operator: the shared
repository, then each consumer's cutover.

## 2. Evidence

(Being filled.)

## 3. Part A: retarget P11 and P12

(Being filled.)

## 4. Part B: one shared gate package

(Being filled.)

## 5. Effect on frozen surfaces and on the trust gate

(Being filled.)

## 6. Slices

(Being filled.)

## 7. Decisions

(Being filled.)

## 8. Not checked

(Being filled.)
