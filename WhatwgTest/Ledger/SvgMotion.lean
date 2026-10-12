import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `SVG-PG-MOTION`

The ten edges of `docs/SVG-MOTION-DAG.md` (`test/contracts/graph-ledger.contract.md`; ruling
R-W6). The graph opened at slice S14 of `docs/SVG-PACKAGE-PLAN.md` (ruling SV-79), when the
motion of a join became one value. Every ground names a theorem, a declaration or a module of
the built tree, and each open item is a named gap or a recorded debt.

The fence is the six modules of motion: the data and its reading, its laws, what holds at every
moment, the order in time, the plan of a join, and the bridge from the reading in whole numbers
to the exact polynomial. The writer of CSS is `Whatwg/Html/Node/SvgMotion.lean`, under the
unrouted prefix `Whatwg.Html` (debt D57): this entry cites its declarations and does not fence
it.

No edge is closed. Ruling R-S29 of `COORDINATION.md` names this graph and changes no edge's
status, so the entry acknowledges it.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The assurance graph of motion as data: its reading, its laws and its writer. -/
def svgMotion : Graph where
  id := "SVG-PG-MOTION"
  document := "docs/SVG-MOTION-DAG.md"
  fence := [`Whatwg.Svg.Scene.Motion, `Whatwg.Svg.Scene.Motion.Laws, `Whatwg.Svg.Scene.Between,
    `Whatwg.Svg.Scene.Score, `Whatwg.Svg.Scene.Plan, `Whatwg.Svg.Geometry.Easing]
  acknowledged := ["R-S29"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the declaration records of motion: no record names each declaration's owner and anchor yet (debt D125)"]
      grounds := [.declarations [`Whatwg.Svg.Scene.Easing, `Whatwg.Svg.Scene.Transition,
        `Whatwg.Svg.Scene.Pose, `Whatwg.Svg.Scene.Change, `Whatwg.Svg.Scene.Track,
        `Whatwg.Svg.Scene.Motion, `Whatwg.Svg.Scene.Plan]]
      note := "A motion is first-order data: a list of tracks, each a key, a change of one kind and a transition. An easing is a list of stops or the two heights of a cubic, in per mille. No function is stored." }
    construction := {
      status := .requiredOpen
      remaining := [
        .named "nothing in the type of a motion says that a thing has one track at most for a property: two shifts on one key are a term"]
      grounds := [.declarations [`Whatwg.Svg.Scene.Motion.ofJoin, `Whatwg.Svg.Scene.Motion.staying,
        `Whatwg.Svg.Scene.Motion.leaving, `Whatwg.Svg.Scene.Plan.moving,
        `Whatwg.Svg.Scene.Plan.and, `Whatwg.Svg.Scene.Motion.within,
        `Whatwg.Svg.Scene.Motion.delayed, `Whatwg.Svg.Scene.Motion.andThen,
        `Whatwg.Svg.Scene.Motion.fit, `Whatwg.Svg.Scene.Motion.reduced,
        `Whatwg.Svg.Scene.Change.morphOf, `Whatwg.Svg.Scene.Transition.per]]
      note := "A step's motion is built from the join of two pictures and a plan: what a kept thing does, how a new thing enters and how an old one leaves. A motion is then held in its step, started later thing by thing, put after another, fitted to a length, or reduced to its ends." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "a moment is a whole thousandth of a step: the reading says nothing of a time between two of them, which a browser draws",
        .named "the reading gives the poses of a key and not what the thing then looks like: no function of the kit puts the poses on a thing, and two poses of one property have no stated meaning (debt D124)"]
      grounds := [.declarations [`Whatwg.Svg.Scene.mix, `Whatwg.Svg.Scene.Easing.at,
        `Whatwg.Svg.Scene.Easing.of, `Whatwg.Svg.Scene.Transition.at, `Whatwg.Svg.Scene.Change.at,
        `Whatwg.Svg.Scene.Track.at, `Whatwg.Svg.Scene.Motion.poses,
        `Whatwg.Svg.Scene.Motion.posesOf, `Whatwg.Svg.Scene.Join.drawn]]
      note := "`Track.at` is the meaning: the pose of a thing at a moment, by the easing of the share of the duration that has passed, with one rounding down. `Join.drawn` says which things a reader draws at a moment of a step." }
    laws := {
      status := .requiredOpen
      remaining := [
        .named "a fact of an easing at whole stops does not reach a transition of a duration other than a thousand, and the duration that a distance asks for has no law of order (debt D126)",
        .named "no law says that a thing that leaves ends as nothing: a plan's `leave` may be any change"]
      grounds := [.theorems [`Whatwg.Svg.Scene.Easing.stopsAt_stop,
        `Whatwg.Svg.Scene.Easing.proper_cubic, `Whatwg.Svg.Scene.Easing.of_thousand,
        `Whatwg.Svg.Scene.Transition.at_done, `Whatwg.Svg.Scene.Track.at_done,
        `Whatwg.Svg.Scene.Motion.within_atRest, `Whatwg.Svg.Scene.Motion.delayed_within_atRest,
        `Whatwg.Svg.Scene.mix_shift, `Whatwg.Svg.Scene.ICubic.mix_move,
        `Whatwg.Svg.Scene.Change.at_morph, `Whatwg.Svg.Scene.mix_gap, `Whatwg.Svg.Scene.mix_mem,
        `Whatwg.Svg.Scene.Easing.bounded_at, `Whatwg.Svg.Scene.Transition.bounded_at,
        `Whatwg.Svg.Scene.Kept.moment, `Whatwg.Svg.Scene.grow_clear,
        `Whatwg.Svg.Scene.Motion.finish_le, `Whatwg.Svg.Scene.Motion.delayed_respects,
        `Whatwg.Svg.Scene.Motion.andThen_respects, `Whatwg.Svg.Scene.Motion.reduced_settles,
        `Whatwg.Svg.Scene.Motion.fit_finish, `Whatwg.Svg.Scene.Motion.fit_respects,
        `Whatwg.Svg.Scene.Motion.mem_staying_key, `Whatwg.Svg.Scene.Motion.mem_leaving_key,
        `Whatwg.Svg.Scene.Motion.staying_end, `Whatwg.Svg.Scene.Motion.ofJoin_end,
        `Whatwg.Svg.Scene.Join.drawn_end]]
      note := "The end law: a track whose transition is over stands at the end of its change, so a step's last moment is the next picture, and with a plan that settles every thing of the new list is then at rest. Between the two pictures: a kept edge that changes its shape by its nodes' transition stays joined to them, and a relation of both pictures is a relation of every moment where the things share one timing and the easing stays in range. In time: a delay by depth, a fit to a length and a reduction to the ends each keep the order that the tracks had." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "no law relates the written sheet to the reading: CSS animations, CSS easing functions, the individual transform properties and `d` as a property are not sealed, and the package holds no model of what a browser computes from them",
        .debt "D119"]
      grounds := [.theorems [`Whatwg.Svg.Scene.Easing.segment_pointAt,
        `Whatwg.Svg.Scene.Easing.cubicAt_eq_floor, `Whatwg.Svg.Scene.Easing.stopsAt_eq_floor,
        `Whatwg.Svg.Scene.Easing.cubicOf_eq_floor, `Whatwg.Svg.Scene.Easing.stopsOf_eq_floor,
        `Whatwg.Svg.Scene.Transition.at_cubic],
        .declarations [`Whatwg.Svg.Scene.Easing.css, `Whatwg.Svg.Scene.Pose.css,
          `Whatwg.Svg.Scene.Motion.keyframes, `Whatwg.Svg.Scene.Motion.animation,
          `Whatwg.Svg.Scene.Motion.sheet, `Whatwg.Svg.Scene.Motion.attrs,
          `Whatwg.Svg.Scene.Motion.attrsAt]]
      note := "An easing of two heights is the curve that CSS names `cubic-bezier(1/3, y1, 2/3, y2)`, whose first coordinate is the progress, and the reading of a transition is that polynomial at the exact share of the duration, rounded down once. A list of stops is what CSS names `linear(…)`. The writer gives each track two keyframes, a duration, a delay and its easing, filled both ways." }
    counterexamples := {
      status := .requiredOpen
      remaining := [
        .named "no register row: the controls of `Whatwg/Svg/Scene/Between.lean`, `Score.lean` and `Plan.lean`, and the three timings of `workshop/BetweenProbe.lean`, are not registered counterexamples"] }
    bridges := {
      status := .requiredOpen
      remaining := [
        .named "one host was observed, by hand: Chrome 152 read every written animation and computed the kit's reading at the moments that `docs/research/2026-10-12-motion-probe/README.md` lists; no harness runs the observation again, and no other engine was observed"] }
    targets := {
      status := .requiredOpen
      remaining := [
        .named "one target, a CSS style sheet inside the picture; a second writer, for a host that does not read `d` as a property or runs no CSS, is not built (debt D125)"]
      grounds := [.modules [`Whatwg.Html.Node.SvgMotion]] }
    trust := {
      status := .requiredOpen
      remaining := [
        .named "the port of lean4-effect4's motion code is this repository's copy of that code on the kit, and no build of lean4-effect4 itself imports the kit"]
      grounds := [.modules [`Whatwg.Svg.Scene.Motion, `Whatwg.Svg.Scene.Motion.Laws,
        `Whatwg.Svg.Scene.Between, `Whatwg.Svg.Scene.Score, `Whatwg.Svg.Scene.Plan,
        `Whatwg.Svg.Geometry.Easing, `Whatwg.Html.Node.SvgMotion, `WhatwgTest.Html.SvgMotion],
        .gate .build]
      note := "The five modules under `Whatwg.Svg.Scene` are under the strict ceiling, `propext` and `Quot.sound` only, with no exact exception (ruling R-S27). `Whatwg.Svg.Geometry.Easing` and the writer are under the ceiling of ruling R-11." }
    coverage := {
      status := .requiredOpen
      remaining := [
        .named "a census of what CSS animations can say, and of what a motion cannot: none exists, and no coverage is claimed"] } }

end WhatwgTest.Ledger
