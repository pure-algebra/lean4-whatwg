import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `SVG-PG-MOTION`

The ten edges of `docs/SVG-MOTION-DAG.md` (`test/contracts/graph-ledger.contract.md`; ruling
R-W6). The graph opened at slice S14 of `docs/SVG-PACKAGE-PLAN.md` (ruling SV-79), when the
motion of a join became one value. Every ground names a theorem, a declaration or a module of
the built tree, and each open item is a named gap or a recorded debt.

The fence is the eleven modules of motion. Nine are under `Whatwg/Svg/Scene/`: the data and its
reading, its laws, what holds at every moment, the order in time, the plan of a join, a step in
stages, the frame of a thing at a moment, what the kept things of a step keep, and a step that
is interrupted. Two are under `Whatwg/Svg/Geometry/`: the bridge
from the reading in whole numbers to the exact polynomial, and the motion at every rational
time. The writer of CSS is `Whatwg/Html/Node/SvgMotion.lean`, under the unrouted prefix
`Whatwg.Html` (debt D57): this entry cites its declarations and does not fence it.

No edge is closed. Rulings R-S29, R-S30 and R-S31 of `COORDINATION.md` name this graph and
change no edge's status, so the entry acknowledges the three.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The assurance graph of motion as data: its reading, its laws and its writer. -/
def svgMotion : Graph where
  id := "SVG-PG-MOTION"
  document := "docs/SVG-MOTION-DAG.md"
  fence := [`Whatwg.Svg.Scene.Motion, `Whatwg.Svg.Scene.Motion.Laws, `Whatwg.Svg.Scene.Between,
    `Whatwg.Svg.Scene.Score, `Whatwg.Svg.Scene.Plan, `Whatwg.Svg.Scene.Stage,
    `Whatwg.Svg.Scene.Frame, `Whatwg.Svg.Scene.Together, `Whatwg.Svg.Scene.Resume,
    `Whatwg.Svg.Geometry.Easing, `Whatwg.Svg.Geometry.Moment, `Whatwg.Svg.Scene.Step,
    `Whatwg.Svg.Scene.Step.Laws, `Whatwg.Svg.Geometry.Spring, `Whatwg.Svg.Geometry.Spring.Laws,
    `Whatwg.Svg.Geometry.Spring.Resume, `Whatwg.Svg.Geometry.Spring.Follow,
    `Whatwg.Svg.Scene.Vector, `Whatwg.Svg.Scene.Machine]
  acknowledged := ["R-S29", "R-S30", "R-S31", "R-S33", "R-S34"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the declaration records of motion: no record names each declaration's owner and anchor yet (debt D125)"]
      grounds := [.declarations [`Whatwg.Svg.Scene.Easing, `Whatwg.Svg.Scene.Transition,
        `Whatwg.Svg.Scene.Pose, `Whatwg.Svg.Scene.Change, `Whatwg.Svg.Scene.Track,
        `Whatwg.Svg.Scene.Motion, `Whatwg.Svg.Scene.Plan, `Whatwg.Svg.Scene.Property,
        `Whatwg.Svg.Scene.Frame, `Whatwg.Svg.Scene.Step, `Whatwg.Svg.Scene.Stages,
        `Whatwg.Svg.Scene.Spring]]
      note := "A motion is first-order data: a list of tracks, each a key, a change of one kind and a transition. An easing is a list of stops or the two heights of a cubic, in per mille. A frame is a value for each of the five properties of a thing. No function is stored." }
    construction := {
      status := .requiredOpen
      remaining := [
        .named "nothing in the type of a motion says that a thing has one track at most for a property: `Motion.Single` says it as a predicate, and it is proved of the step of a plan that changes no property twice (`Motion.single_ofJoin`); a motion that a caller builds by hand has no such proof"]
      grounds := [.declarations [`Whatwg.Svg.Scene.Motion.ofJoin, `Whatwg.Svg.Scene.Motion.staying,
        `Whatwg.Svg.Scene.Motion.leaving, `Whatwg.Svg.Scene.Plan.moving,
        `Whatwg.Svg.Scene.Plan.and, `Whatwg.Svg.Scene.Motion.within,
        `Whatwg.Svg.Scene.Motion.delayed, `Whatwg.Svg.Scene.Motion.andThen,
        `Whatwg.Svg.Scene.Motion.fit, `Whatwg.Svg.Scene.Motion.reduced,
        `Whatwg.Svg.Scene.Motion.slotted, `Whatwg.Svg.Scene.Motion.staged,
        `Whatwg.Svg.Scene.Change.morphOf, `Whatwg.Svg.Scene.Transition.per,
        `Whatwg.Svg.Scene.Plan.Single, `Whatwg.Svg.Scene.Plan.MovesBy,
        `Whatwg.Svg.Scene.Plan.resume, `Whatwg.Svg.Scene.Plan.sprout,
        `Whatwg.Svg.Scene.Change.from, `Whatwg.Svg.Scene.Frame.toRest,
        `Whatwg.Svg.Scene.Step.motion, `Whatwg.Svg.Scene.Step.planned,
        `Whatwg.Svg.Scene.Step.staged, `Whatwg.Svg.Scene.Step.next,
        `Whatwg.Svg.Scene.Step.interrupt, `Whatwg.Svg.Scene.Spring.critical,
        `Whatwg.Svg.Scene.Spring.under, `Whatwg.Svg.Scene.Spring.easing,
        `Whatwg.Svg.Scene.Spring.resumed, `Whatwg.Svg.Scene.Plan.moveBy,
        `Whatwg.Svg.Scene.Plan.springResume]]
      note := "A step's motion is built from the join of two pictures and a plan: what a kept thing does, how a new thing enters and how an old one leaves. A motion is then held in its step, started later thing by thing, put after another, fitted to a length, reduced to its ends, or put in stages: the kept things first, then the new things level by level, each level in a slot of its own." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "the exact reading is stated at every rational time, for a value, a gap and a kept relation: no law speaks of a real time or of a limit, and a size that grows past its end has no exact form",
        .named "a frame does not know a thing's own shape: `Frame.AtRest` says nothing of the shape, and a thing whose shape a track changed keeps the last one given; of a step it is known under a premise (`Step.frame_shape`: a thing of the new picture has its own shape at every moment where the plan changes no shape)",
        .named "a thing inside a group that moves has its own frame and its group's, and no function puts the one inside the other"]
      grounds := [.declarations [`Whatwg.Svg.Scene.mix, `Whatwg.Svg.Scene.Easing.at,
        `Whatwg.Svg.Scene.Easing.of, `Whatwg.Svg.Scene.Transition.at, `Whatwg.Svg.Scene.Change.at,
        `Whatwg.Svg.Scene.Track.at, `Whatwg.Svg.Scene.Motion.poses,
        `Whatwg.Svg.Scene.Motion.posesOf, `Whatwg.Svg.Scene.Join.drawn,
        `Whatwg.Svg.Scene.Pose.onto, `Whatwg.Svg.Scene.Motion.frame,
        `Whatwg.Svg.Scene.Motion.Same, `Whatwg.Svg.Scene.Frame.Shows,
        `Whatwg.Svg.Scene.Frame.stand, `Whatwg.Svg.Scene.Easing.exact,
        `Whatwg.Svg.Scene.Transition.exact, `Whatwg.Svg.Scene.mixExact,
        `Whatwg.Svg.Scene.Step.drawn, `Whatwg.Svg.Scene.Step.frame, `Whatwg.Svg.Scene.Step.sample,
        `Whatwg.Svg.Scene.Spring.run, `Whatwg.Svg.Scene.Spring.interrupted,
        `Whatwg.Svg.Scene.Spring.followed, `Whatwg.Svg.Scene.Easing.table,
        `Whatwg.Svg.Scene.Transition.table, `Whatwg.Svg.Scene.Track.table,
        `Whatwg.Svg.Scene.fdiv, `Whatwg.Svg.Scene.Track.at?]]
      note := "`Track.at` is the meaning of a track: the pose of a thing at a moment, by the easing of the share of the duration that has passed, with one rounding down. `Motion.frame` is the meaning of a motion for one thing: its poses put on the still picture in the order of the tracks, a later pose of one property in place of an earlier one. `Join.drawn` says which things a reader draws at a moment of a step. `Transition.exact` and `mixExact` are the same readings in rational numbers at a rational time, and the whole-number readings are their floors." }
    laws := {
      status := .requiredOpen
      remaining := [
        .named "a fact of an easing at whole stops does not reach a transition of a duration other than a thousand, and the duration that a distance asks for has no law of order (debt D126)",
        .named "no law says that a thing that leaves ends as nothing: a plan's `leave` may be any change",
        .named "`Motion.Same` is kept by `++` in its second part only where both rows are `Single`: the law without that premise is false, and an example of `Frame.lean` refutes it",
        .named "a step in stages has no order inside one level: with lean4-effect4's shares a new edge and the box at its end overlap by a twentieth of the slot",
        .named "a step resumed with speed (`Plan.springResume`) keeps the gaps of its pictures in exact places only (`Spring.critical_followed_gap`): each thing then takes an easing of its own, so `Motion.together` does not reach its whole-number frames, and the law waits for a change through way points or for shifts that add (debt D134)",
        .named "a step in stages that interrupts another has no law of its first moment: `Track.endBy` rounds a short duration to nothing (control in `Whatwg/Svg/Scene/Step/Laws.lean`)",
        .named "no law of frames says that a new thing of a staged step is not seen before its level",
        .named "the law of the kept things of a step is of two kept things at whole moments: a kept thing against a new or a leaving one, and the same law at a rational time, are not stated for a step"]
      grounds := [.theorems [`Whatwg.Svg.Scene.Easing.stopsAt_stop,
        `Whatwg.Svg.Scene.Easing.proper_cubic, `Whatwg.Svg.Scene.Easing.of_thousand,
        `Whatwg.Svg.Scene.Transition.at_done, `Whatwg.Svg.Scene.Track.at_done,
        `Whatwg.Svg.Scene.Motion.within_atRest, `Whatwg.Svg.Scene.Motion.within_after,
        `Whatwg.Svg.Scene.Motion.delayed_within_atRest,
        `Whatwg.Svg.Scene.mix_shift, `Whatwg.Svg.Scene.ICubic.mix_move,
        `Whatwg.Svg.Scene.Change.at_morph, `Whatwg.Svg.Scene.mix_gap, `Whatwg.Svg.Scene.mix_mem,
        `Whatwg.Svg.Scene.Easing.bounded_at, `Whatwg.Svg.Scene.Transition.bounded_at,
        `Whatwg.Svg.Scene.Kept.moment, `Whatwg.Svg.Scene.grow_clear,
        `Whatwg.Svg.Scene.Motion.finish_le, `Whatwg.Svg.Scene.Motion.delayed_respects,
        `Whatwg.Svg.Scene.Motion.andThen_respects, `Whatwg.Svg.Scene.Motion.reduced_settles,
        `Whatwg.Svg.Scene.Motion.fit_finish, `Whatwg.Svg.Scene.Motion.fit_respects,
        `Whatwg.Svg.Scene.Motion.mem_staying_key, `Whatwg.Svg.Scene.Motion.mem_leaving_key,
        `Whatwg.Svg.Scene.Motion.staying_end, `Whatwg.Svg.Scene.Motion.ofJoin_end,
        `Whatwg.Svg.Scene.Join.drawn_end, `Whatwg.Svg.Scene.Motion.staged_kept_first,
        `Whatwg.Svg.Scene.Motion.staged_levels, `Whatwg.Svg.Scene.Motion.staged_end,
        `Whatwg.Svg.Scene.Motion.staged_untimed, `Whatwg.Svg.Scene.Pose.onto_comm,
        `Whatwg.Svg.Scene.Pose.onto_onto, `Whatwg.Svg.Scene.Frame.ofPoses_congr,
        `Whatwg.Svg.Scene.Motion.frame_has, `Whatwg.Svg.Scene.Motion.frame_shift,
        `Whatwg.Svg.Scene.Motion.frame_of_no_track, `Whatwg.Svg.Scene.Motion.within_frame_atRest,
        `Whatwg.Svg.Scene.Motion.Same.of_mem, `Whatwg.Svg.Scene.Motion.Same.append_comm,
        `Whatwg.Svg.Scene.Transition.exact_mem, `Whatwg.Svg.Scene.Transition.exact_gap,
        `Whatwg.Svg.Scene.KeptExact.moment, `Whatwg.Svg.Scene.KeptExact.along,
        `Whatwg.Svg.Scene.Transition.mix_near, `Whatwg.Svg.Scene.Motion.single_ofJoin,
        `Whatwg.Svg.Scene.Motion.together, `Whatwg.Svg.Scene.Motion.ofJoin_together,
        `Whatwg.Svg.Scene.Motion.staged_together, `Whatwg.Svg.Scene.Motion.staged_leftOf,
        `Whatwg.Svg.Scene.Plan.resume_settles, `Whatwg.Svg.Scene.Plan.resume_of_rest,
        `Whatwg.Svg.Scene.Motion.resume_end, `Whatwg.Svg.Scene.Motion.nothing_jumps,
        `Whatwg.Svg.Scene.Motion.nothing_moves, `Whatwg.Svg.Scene.Motion.resume_leaving_held,
        `Whatwg.Svg.Scene.Step.frame_end, `Whatwg.Svg.Scene.Step.sample_end_rest,
        `Whatwg.Svg.Scene.Step.single, `Whatwg.Svg.Scene.Step.together,
        `Whatwg.Svg.Scene.Step.order, `Whatwg.Svg.Scene.Step.kept_rest,
        `Whatwg.Svg.Scene.Step.nothing_jumps, `Whatwg.Svg.Scene.Step.nothing_moves,
        `Whatwg.Svg.Scene.Step.interrupt_of_rest, `Whatwg.Svg.Scene.Spring.run_moved,
        `Whatwg.Svg.Scene.Spring.run_tail, `Whatwg.Svg.Scene.Spring.critical_easing_bounded,
        `Whatwg.Svg.Scene.Spring.critical_interrupted_gap,
        `Whatwg.Svg.Scene.Spring.critical_followed_gap,
        `Whatwg.Svg.Scene.Motion.springResume_end,
        `Whatwg.Svg.Scene.Motion.springResume_nothing_moves,
        `Whatwg.Svg.Scene.fdiv_eq, `Whatwg.Svg.Scene.mix_fdiv,
        `Whatwg.Svg.Scene.Easing.cubicOf_fdiv, `Whatwg.Svg.Scene.Easing.stopsOf_fdiv,
        `Whatwg.Svg.Scene.Track.at?_eq, `Whatwg.Svg.Scene.Track.at?_sound,
        `Whatwg.Svg.Scene.Track.table_machine, `Whatwg.Svg.Scene.Track.eq_of_table]]
      note := "The end law: a track whose transition is over stands at the end of its change, so a step's last moment is the next picture, and with a plan that settles every thing of the new list then looks as the still picture has it. Between the two pictures: a kept edge that changes its shape by its nodes' transition stays joined to them, and a relation of both pictures is a relation of every whole moment, and of every rational time in exact numbers, where the things share one timing and the easing stays in range. In time: a delay by depth, a fit to a length, a reduction to the ends and a step in stages each keep the order that the tracks had, and in a staged step no new thing appears before the kept things are at rest. Of a thing: where no thing has two tracks of one property, its frame shows the pose of each of its tracks and does not depend on their order. Of a whole step: kept things that take one transition with an easing in range keep, where they stand at every moment, each relation that their places have in both pictures. Of an interruption: at the first moment of a step that resumes from where things are seen, each kept thing shows every pose that it showed and stands where it stood, and the step ends on the next picture." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "no law relates the written sheet to the reading: CSS animations, CSS easing functions, the individual transform properties and `d` as a property are not sealed, and the package holds no model of what a browser computes from them",
        .debt "D119"]
      grounds := [.theorems [`Whatwg.Svg.Scene.Easing.segment_pointAt,
        `Whatwg.Svg.Scene.Easing.cubicAt_eq_floor, `Whatwg.Svg.Scene.Easing.stopsAt_eq_floor,
        `Whatwg.Svg.Scene.Easing.cubicOf_eq_floor, `Whatwg.Svg.Scene.Easing.stopsOf_eq_floor,
        `Whatwg.Svg.Scene.Transition.at_cubic, `Whatwg.Svg.Scene.Easing.of_eq_floor,
        `Whatwg.Svg.Scene.Transition.at_eq_floor, `Whatwg.Svg.Scene.mix_eq_floor_exact],
        .declarations [`Whatwg.Svg.Scene.Easing.css, `Whatwg.Svg.Scene.Pose.css,
          `Whatwg.Svg.Scene.Frame.css, `Whatwg.Svg.Scene.Motion.keyframes,
          `Whatwg.Svg.Scene.Motion.animation, `Whatwg.Svg.Scene.Motion.sheet,
          `Whatwg.Svg.Scene.Motion.attrs, `Whatwg.Svg.Scene.Motion.attrsAt,
          `Whatwg.Svg.Scene.Motion.rules, `Whatwg.Svg.Scene.Motion.decls,
          `Whatwg.Html.Play, `Whatwg.Svg.Scene.Step.nodes, `Whatwg.Svg.Scene.Step.still]]
      note := "An easing of two heights is the curve that CSS names `cubic-bezier(1/3, y1, 2/3, y2)`, whose first coordinate is the progress, and the reading of a transition is that polynomial at the exact share of the duration, rounded down once. A list of stops is what CSS names `linear(…)`. The writer gives each change under each easing one rule of two keyframes with the easing in it, and each track a duration and a delay, filled both ways; its times are written exactly, to a thousandth of a millisecond; a step can be opened at a moment, running or paused, or at the moment that a custom property says; and the sheet can end every animation at once for a reader who asks for reduced motion. Since slice S17 the sheet and a thing's declarations are data before they are text (`Whatwg/Html/Node/Css.lean`)." }
    counterexamples := {
      status := .requiredOpen
      remaining := [
        .named "no register row: the controls of `Whatwg/Svg/Scene/Between.lean`, `Score.lean`, `Plan.lean`, `Stage.lean` and `Frame.lean`, the controls of `Whatwg/Svg/Geometry/Moment.lean`, and the timings of `workshop/BetweenProbe.lean`, are not registered counterexamples"] }
    bridges := {
      status := .requiredOpen
      remaining := [
        .named "one host was observed, by hand: Chrome 152 read every written animation and computed the kit's reading at the moments that `docs/research/2026-10-12-motion-probe/README.md` lists, at 998 times that are no whole moments, and in its own paused pictures of five moments beside the kit's; slice S17 added the rule of reduced motion, a step that a custom property scrubs, and a step resumed with its speed to what was observed; no harness runs the observations again, and no other engine was observed"] }
    targets := {
      status := .requiredOpen
      remaining := [
        .named "one target is written by this package, a CSS style sheet inside the picture; a second writer, for a host that does not read `d` as a property or runs no CSS, is not built (debt D125). For a player that samples the tracks itself, slice S18 gives the readings as tables and in a form a 64-bit machine computes (`Whatwg/Svg/Scene/Vector.lean`, `Machine.lean`), and a C transcription that one compiler ran against the table; no theorem is about C"]
      grounds := [.modules [`Whatwg.Html.Node.SvgMotion, `Whatwg.Html.Node.Css,
        `Whatwg.Html.Node.SvgStep]] }
    trust := {
      status := .requiredOpen
      remaining := [
        .named "the port of lean4-effect4's motion code is this repository's copy of that code on the kit, and no build of lean4-effect4 itself imports the kit's motion yet"]
      grounds := [.modules [`Whatwg.Svg.Scene.Motion, `Whatwg.Svg.Scene.Motion.Laws,
        `Whatwg.Svg.Scene.Between, `Whatwg.Svg.Scene.Score, `Whatwg.Svg.Scene.Plan,
        `Whatwg.Svg.Scene.Stage, `Whatwg.Svg.Scene.Frame, `Whatwg.Svg.Scene.Together,
        `Whatwg.Svg.Scene.Resume, `Whatwg.Svg.Geometry.Easing,
        `Whatwg.Svg.Geometry.Moment, `Whatwg.Html.Node.SvgMotion, `WhatwgTest.Html.SvgMotion,
        `Whatwg.Svg.Scene.Step, `Whatwg.Svg.Scene.Step.Laws, `Whatwg.Svg.Geometry.Spring,
        `Whatwg.Svg.Geometry.Spring.Laws, `Whatwg.Svg.Geometry.Spring.Resume,
        `Whatwg.Svg.Geometry.Spring.Follow, `Whatwg.Svg.Scene.Vector,
        `Whatwg.Svg.Scene.Machine, `Whatwg.Html.Node.Css, `Whatwg.Html.Node.SvgStep,
        `WhatwgTest.Html.SvgStep, `WhatwgTest.Html.SvgSpring, `WhatwgTest.Html.SvgSpringResume],
        .gate .build]
      note := "The thirteen modules under `Whatwg.Svg.Scene` are under the strict ceiling, `propext` and `Quot.sound` only, with no exact exception (ruling R-S27). The six under `Whatwg.Svg.Geometry` and the writer are under the ceiling of ruling R-11." }
    coverage := {
      status := .requiredOpen
      remaining := [
        .named "a census of what CSS animations can say, and of what a motion cannot: none exists, and no coverage is claimed"] } }

end WhatwgTest.Ledger
