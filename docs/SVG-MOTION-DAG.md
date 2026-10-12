# SVG motion assurance graph (`SVG-PG-MOTION`)

Status: open, 2026-10-12. This document owns the graph for motion as data: what a motion means
at a moment, the laws of that meaning, and the style sheet that the kit writes from it.
`docs/SVG-PACKAGE-PLAN.md` owns the slices and the rulings SV-60 to SV-80, which settled the
design.

The graph opened at slice S14. Before it the modules of motion were declarations of the leaf
`SVG-LF-GRAMMAR`. A motion has a reading, laws of composition and a writer to a second language.
Each of the three needs a proof graph (`docs/AGENT-ROUTING.md`, "Assurance threshold"): a
denotation, a composition law and a generated-code relation. A leaf record has no place to say
what is open.

**Authority.** No standard owns the meaning of a motion. The meaning is the kit's own reading,
`Track.at`: the pose of a thing at a whole thousandth of a step, in whole numbers, with one
rounding down. The writer's target is CSS: its animations, its easing functions, its individual
transform properties, and `d` as a property. None of those texts is sealed under `vendor/`
(debt D119), so no theorem of this graph names an algorithm of CSS.

**Fence.** The graph owns six modules. Five are under `Whatwg/Svg/Scene/`, the layer with no
rational number and the strict axiom ceiling: `Motion` (the data and its reading), `Motion/Laws`,
`Between` (what holds at every moment), `Score` (order in time) and `Plan` (the motion of a join
as one value). The sixth is `Whatwg/Svg/Geometry/Easing`, which says that the reading in whole
numbers is the exact polynomial, rounded down once. The writer `Whatwg/Html/Node/SvgMotion` stays
under the unrouted prefix `Whatwg.Html` (debt D57): this graph cites it and does not own it. The
things that a motion acts on are passive data and are the leaf `SVG-LF-SCENE`: a thing that
moves, the join by key, a tree, a share, a scale, a face's metrics and a label.

**Observation.** There is one observation, the reading. `Motion.posesOf m key t` is the list of
poses that the tracks of `m` set on the thing `key` at the moment `t`, a whole number of
thousandths of the step. A law that says "at every moment" says it of these moments: 0, 1 and
so on to 1000, and every whole moment after. No host runs in this graph. What a browser computes
from the written sheet is a host observation, recorded under the bridges edge.

## Current state

The status of every edge of this graph is recorded in the ledger module
`WhatwgTest/Ledger/SvgMotion.lean`, rendered to `generated/graphs/SVG-PG-MOTION.md` by
`lake exe whatwg_ledger --write`, and checked by `lake exe whatwg_ledger`. The history of this
document is in `docs/receipts/SVG-PG-MOTION.md`.

## Claim scope

- A moment is a whole thousandth of a step. A browser also draws the times between two of them,
  and no law of this graph speaks of those. The exact eased progress at a rational share of a
  transition is `Easing.cubicExact`, and the reading is its floor (`Transition.at_cubic`); a law
  at every rational time is not stated yet.
- The reading rounds down once. A program that needs the pose to within less than a unit reads
  the exact geometry of `Whatwg/Svg/Geometry/` and not this layer.
- `Kept.moment` says that a relation of both pictures is a relation of every moment under two
  premises: the things share one timing, and the easing stays in range. Each premise has a
  control in `Whatwg/Svg/Scene/Between.lean` where the relation fails without it.
- A motion is a list of tracks. Nothing in its type says that a thing has one track at most for
  a property. Where it has two, the reading gives both poses in order, and CSS shows the later
  one. No law says so yet, and no function of the kit puts the poses on a thing (debt D124).
- No law relates the written sheet to the reading. One browser was observed by hand, at the
  moments that `docs/research/2026-10-12-motion-probe/README.md` lists, and no harness runs the
  observation again.
- A plan says how the things of a join move. Nothing asks that a thing that leaves ends as
  nothing: the caller chooses a change that does.
- `Motion.fit` and `Motion.delayed` keep an order in time that the tracks had. They do not
  invent one: a caller says which thing comes from which.
- An easing that settles by a moment (`Easing.settledBy`) is a fact of a transition of a
  thousand. It does not reach a transition of another duration (debt D126).
