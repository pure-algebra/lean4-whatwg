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

**Fence.** The graph owns eleven modules. Nine are under `Whatwg/Svg/Scene/`, the layer with no
rational number and the strict axiom ceiling: `Motion` (the data and its reading), `Motion/Laws`,
`Between` (what holds at every moment), `Score` (order in time), `Plan` (the motion of a join
as one value), `Stage` (a step in stages), `Frame` (what a thing looks like at a moment),
`Together` (what the kept things of a step keep) and `Resume` (a step that is interrupted). Two
are under `Whatwg/Svg/Geometry/`: `Easing`, which says that the reading in whole numbers is the
exact polynomial, rounded down once, and `Moment`, the motion at every rational time. The writer
`Whatwg/Html/Node/SvgMotion` stays
under the unrouted prefix `Whatwg.Html` (debt D57): this graph cites it and does not own it. The
things that a motion acts on are passive data and are the leaf `SVG-LF-SCENE`: a thing that
moves, the join by key, a tree and its edits, a share, a row, a scale, a face's metrics, a
label, the crossings of lines and lanes of states.

**Observation.** There is one observation, the reading. `Motion.frame m key t` is what the thing
`key` looks like at the moment `t`, a whole number of thousandths of the step: the poses that the
tracks of `m` set on it (`Motion.posesOf`), put on the still picture in the order of the tracks.
A law that says "at every moment" says it of these moments: 0, 1 and so on to 1000, and every
whole moment after. A law of `Whatwg/Svg/Geometry/Moment.lean` says "at every rational time",
and says it of the exact reading, of which the whole-number reading is the floor. No host runs
in this graph. What a browser computes from the written sheet is a host observation, recorded
under the bridges edge.

## Current state

The status of every edge of this graph is recorded in the ledger module
`WhatwgTest/Ledger/SvgMotion.lean`, rendered to `generated/graphs/SVG-PG-MOTION.md` by
`lake exe whatwg_ledger --write`, and checked by `lake exe whatwg_ledger`. The history of this
document is in `docs/receipts/SVG-PG-MOTION.md`.

## Claim scope

- A moment is a whole thousandth of a step. A browser also draws the times between two of them.
  Since slice S15 the laws of a gap, of a bound and of a kept relation are stated at every
  rational time, in exact numbers (`Transition.exact_gap`, `KeptExact.moment`), and the reading
  in whole numbers is the floor of the exact one (`Transition.at_eq_floor`), within a unit and a
  thousandth of the travel (`Transition.mix_near`). No law speaks of a real time or of a limit.
- The reading rounds down once. A program that needs the pose to within less than a unit reads
  the exact geometry of `Whatwg/Svg/Geometry/` and not this layer.
- `Kept.moment` says that a relation of both pictures is a relation of every moment under two
  premises: the things share one timing, and the easing stays in range. Each premise has a
  control in `Whatwg/Svg/Scene/Between.lean` where the relation fails without it.
- A motion is a list of tracks. Nothing in its type says that a thing has one track at most for
  a property (`Motion.Single` says it as a predicate). Where a thing has two, `Motion.frame`
  shows the later one, as CSS does, and the frame then depends on the order of the tracks.
- Two motions are the same to a reader (`Motion.Same`) where every thing has one frame in both
  at every moment. That is kept when a motion is put after both. It is kept when one is put
  before both only where no thing has two tracks of one property.
- A step in stages keeps the kept things first and the levels in order. It keeps no order
  inside one level.
- The law of the kept things of a step (`Motion.together`) asks one transition for their
  places and an easing that passes `Easing.bounded`. It is of two kept things, at whole
  moments. A kept thing against a new one is a case of the general law and has no statement
  for a step.
- A step that resumes starts each thing where it is seen and from standing: nothing is said of
  its speed. A kept thing whose shape was changing jumps to its own shape where the plan gives
  no change of shape and its own shape is not given.
- No law relates the written sheet to the reading. One browser was observed by hand, at the
  moments that `docs/research/2026-10-12-motion-probe/README.md` lists, and no harness runs the
  observation again.
- A plan says how the things of a join move. Nothing asks that a thing that leaves ends as
  nothing: the caller chooses a change that does.
- `Motion.fit` and `Motion.delayed` keep an order in time that the tracks had. They do not
  invent one: a caller says which thing comes from which.
- An easing that settles by a moment (`Easing.settledBy`) is a fact of a transition of a
  thousand. It does not reach a transition of another duration (debt D126).
