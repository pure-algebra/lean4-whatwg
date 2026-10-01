# W9 design: `Ecma262.Agent`, one step function, an `Effects` face

Status: research record of the W9 design seat of review lane W (rulings
R-W0 and R-W1 in `COORDINATION.md`). It recommends a design and states the
decisions it leaves to the coordinator. It makes no Model Claim, closes no
graph edge, changes no disposition and moves no coverage row.

Draft 1 (skeleton). Sections marked "unmeasured" are filled by later
commits on `review/w9-agent-design`.

| Subject | Pin |
| --- | --- |
| this repository | `main` at `97a871522ce18f792449f51300c9d93288abb398` |
| lean4-effect4 | `refactor/phase1-phase3` at `efcf1ae2f4d4ef7b599e5038572c66a977fe35b2` |
| `effects` | `a4ee7a14248ee5976039b73039319efa87834986` (v0.8.0), both repositories |
| toolchain | `leanprover/lean4:v4.33.1` |

Evidence labels follow the review: `[C]` measured by this seat, with its
command; `[S]` read in source; `[H]` a hypothesis not tried.

## 1. Recommendation

Provisional; amended once the prototype and the lean4-effect4 re-read land.

1. Add one record, `Whatwg.Ecma262.Agent.Agent value reason body`, that
   *contains* the landed `Promise.Table`, `Promise.Reactions` and
   `Jobs.Queue (Jobs.ReactionJob (Except reason value))`, plus the store of
   resolving functions (the one-shot markers), the activation
   `Jobs.Active`, the settlement trace, and the function cursor. Nothing
   landed is replaced; every landed operation becomes a named view.
2. Give it one total step function over a first-order operation alphabet,
   `Agent.step : Agent v r b → Op v r b → Agent v r b × Op.Answer op`,
   whose disabled branches return the agent unchanged with a `none` answer
   (decision 7's guarded-total style, DB-07's live frontier).
3. Repair D46 additively: `Agent.resolve` and `Agent.reject` go through the
   capability's resolving functions *and* `Table.settleAndTrigger`, so a
   `react` followed by a `resolve` enqueues the reaction's job in FIFO
   position. The frozen `WebIdl.Promise.resolve` is re-described as the table
   projection of the agent operation under the well-formedness predicate.
4. State `Agent.WF` (identities unique, every cursor ahead of every stored
   identity, every stored reference allocated, resolved functions only on
   settled promises) and prove that every operation keeps it.
5. Put the `Effects.Signature` face in its own module tree,
   `Whatwg.Effects.*`, in its own Lake library, `WhatwgEffects`, under the
   strict ceiling, so the data model never imports `Effects` and a consumer
   that wants only the record does not build it.
6. Run it as a promise slice of its own (Q5), owned by an amended
   `docs/PROMISE-DAG.md`, before P8 proper; W8's transition kernel and the
   Q4 configuration's one-table cutover build on the record.

## 2. Evidence

Unmeasured in this draft except where labelled.

- `[C]` `lake build` at the base: 386 jobs, gate line "checked 222 source
  files and 16723 declarations", `Classical.choice` reached by 0
  declarations under the five strict prefixes.
- `[C]` `lake exe whatwg_census --standard ecma262 --report`: denominator
  75, owned-with-green 0/75, absent 75.

### 2.1 Re-verification of the review's "Fit with lean4-effect4"

Unmeasured.

## 3. Public declaration record

Unmeasured: signatures are filled from the prototype as they elaborate.

## 4. Effect on frozen surfaces

Unmeasured.

## 5. Effect on the trust gate, the strict ceiling and the Lake libraries

Unmeasured.

## 6. Slices

Unmeasured.

## 7. Decisions for the coordinator

Unmeasured.

## 8. Not checked

Unmeasured.
