import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Node.SvgKeyword
import Whatwg.Svg.Scene.Frame
import Whatwg.Html.Node.Css

/-!
# Whatwg.Html.Node.SvgMotion

Owner: the motion of a step as CSS (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-65; the
interface of slice S17).

`Whatwg/Svg/Scene/Motion.lean` has the motion of a step as data: a list of tracks, each a key,
a change and a transition. A program that draws every moment itself reads a track with
`Track.at`. A browser can draw the moments: this module writes the same tracks as CSS
animations, so a step is one picture and its tracks, and no row of pictures.

```
let m := (Motion.ofJoin key j plan).within         -- the tracks of a join: `Scene/Plan.lean`
let play : Play := { step := 600, stem := "s3" }   -- how the step is played, said once
Svg.svg [] (m.sheetNode play :: marks)             -- the sheet of the step, as one node
Svg.path d (m.attrs k play)                        -- the thing with the key `k`
Svg.g (m.attrs k play [("cursor", "pointer")]) …   -- a thing with a style of its own
```

`Play` says how a step is played: how long it is, the stem of its names, the grid of its
counts, the moment it is opened at, whether it stands still there, whether one number scrubs
it, and when a reader sees its end with no motion. Every writer here takes the one record, so
the sheet and the things of a step cannot disagree, and a caller names what it changes.

What is written, as data (`Whatwg/Html/Node/Css.lean`) and then as text:

- **The sheet** (`Motion.rules`, `Motion.sheet`, `Motion.sheetNode`): one rule
  `@keyframes s3-i { from { …; animation-timing-function: <easing> } to { … } }` for each
  change of the step under each easing, with the two poses of the change. Tracks with one
  change and one easing share one rule, whatever their keys and their times, and `i` is the
  place of the first of them (`Motion.ruleIndex`). A shift is the property `translate`, a size
  is `scale`, an opacity is `opacity`, and a part revealed is `stroke-dashoffset`.
- **The easing** stands in the rule, at its first keyframe. The easing of a keyframe is the
  easing of the way from it to the next, and a rule here has two keyframes, so it is the easing
  of the whole animation. An easing is long, and many things share one: it is written once for
  each rule, and not once for each thing. `Easing.stops` is `linear(…)`, the two stops `0` and
  `1` are the keyword `linear`, and `Easing.cubic y1 y2` is
  `cubic-bezier(0.333333, y1, 0.666667, y2)`.
- **On a thing** (`Motion.decls`, `Motion.attrs`): one `style` attribute. It holds
  `animation: s3-i <duration> <delay> both` for each track of the thing, and what the changes
  need beside it. The caller's own declarations are merged into it (`Css.Decls.merge`): the
  thing has one `style`, and where both say a property the step's stands. Filling both ways
  shows the start until the delay is over and the end afterwards, as `Transition.at` reads.
- **A line that is revealed** has the `pathLength` of a thousand, one dash of two thousand and
  a gap of two thousand, and the dash is offset by two thousand less the part. So a part from
  a thousand below nothing to two thousand is drawn as `Pose.reveal` says: an easing that goes
  past its end draws the whole line, and hides none of its start.
- **A change of shape** as the property `d`, a `path("…")` at each end, every segment a `C`.
  A browser goes from one path to another of the same commands point by point, which is
  `ICubic.mix`. The two ends of a change are written with the same commands: a subpath starts
  wherever either of them starts one (`Change.ends`). A closed outline that is filled looks the
  same with a subpath more; a stroke has two ends there in place of a join. Not every browser
  reads `d` as a property: Chrome 152 does, by observation; one that does not shows the thing's
  own shape throughout, which is the shape at the end.
- **Reduced motion** (`Play.reduce`, `Play.reduced`): the sheet holds one rule that ends every
  animation of the step at once, with a duration and a delay of nothing. By default it stands
  in `@media (prefers-reduced-motion: reduce)`. An animation that fills both ways then shows
  its end, so a reader who asked for reduced motion sees the last moment of the step and no
  moment before it. The kit reads that moment as `Motion.frame m key 1000`. The end laws say
  that it is the next picture: every pose of a thing of the new picture is at rest there
  (`Motion.ofJoin_end` of `Whatwg/Svg/Scene/Plan.lean`, `Motion.staged_end` and
  `Motion.staged_within_end` of `Whatwg/Svg/Scene/Stage.lean`, and `Motion.frame_atRest`). A
  `style` element inside a picture holds for the whole page, and a declaration of a `style`
  attribute stands over a declaration of a sheet unless that one is `!important`. So the two
  declarations of the rule are `!important`, and its selector hits the things of this step
  alone: each thing that moves carries the attribute `data-motion` with the stem (`Play.mark`,
  `Motion.mark_mem`). A step that stands still is a still picture already, and its things carry
  no mark.
- **A step that one number scrubs** (`Play.scrub`, `Play.scrubbed`): each delay is
  `calc((<delay> - var(--t, <opened>)) * <a per mille of the step>)`. With the animations
  paused, the picture shows the moment that the custom property `--t` says, from `0` to `1000`,
  wherever an ancestor sets it (`Play.at`), and the moment `opened` where none does. A slider or
  a scroll position that sets the one property scrubs the whole step, with no script for each
  thing. The kit reads the picture at `--t: t` as `Motion.frame m key t`.

`translate` and `scale` are properties of their own in CSS Transforms 2, so a shift and a size
on one thing do not replace each other, and neither replaces a `transform` attribute.

`Motion.declsAt`, `Motion.stillStyle?` and `Motion.attrsAt` write a moment with no animation,
and `Frame.decls`, `Frame.css` and `Frame.attrs` write a frame.

What the laws say. Every animation that a thing is given names a rule of the sheet, and that
rule holds the two ends of the track's change and its easing (`Motion.rule_mem`). Two changes
of a step, or one change under two easings, have two places, so no rule of the sheet stands
for two of them (`Motion.ruleIndex_inj`). A thing with a track has declarations
(`Motion.decls_ne_nil`), and in a step that runs under a rule of reduced motion it carries the
mark that the rule selects (`Motion.mark_mem`). These laws are about what is written, and none
is about what a browser draws. They depend on `propext`, `Quot.sound` and `Classical.choice` at
most; the last comes in with the text functions of core, as it does for the writers
themselves.

Nothing under `Whatwg/Svg/Scene/` knows of CSS. The property that scrubs a step, the rule of
reduced motion, the stem and the mark are of this writer and of its `Play` alone, so a player
that reads the tracks with no browser reads the same data as this writer does.

What this module does not claim. The text is written by rule and read back by nothing: no
grammar of CSS is sealed in this repository, so no gate judges it (debt D119). A browser
computes in floating point; it reads `1/3` at six places; and between two stops of `linear()`
it draws the straight line that `Easing.stopsAt` rounds down. Two tracks of one kind on one key
write one property twice, and the later one wins: `Motion.frame` of
`Whatwg/Svg/Scene/Frame.lean` reads a thing the same way. A stem is written as it is, in the
names of the rules and in a selector: it is a letter and then letters, digits and `-`. A thing
that grows is given `transform-box` and `transform-origin`, and these also move the origin of a
`transform` attribute on the same element: a thing with a `transform` that is no translation
takes its motion on a group around it. A caller's own `animation` on a thing gives way to the
step's, as any property does that both say. The easing of a keyframe, the rule of reduced
motion, the delay of a scrubbed step and the dash of two thousand are written by rule, from
what their writer remembers of CSS: no browser read them here.

Since slice S15 (ruling SV-86) a step can be opened at a moment (`opened`), running or `paused`: the delay of
each animation is that much less, and a delay of less than nothing starts an animation partway
through. A page that is loaded again in the middle of a step goes on from there, and a paused
one is the browser's own still picture of the moment, with no script.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Value (Cubic)
open Whatwg.Svg.Scene (IVec ICubic Easing Transition Pose Change Track Motion Frame)

namespace Css

/-- A count of thousandths as a CSS number: `1567` is `1.567`, `-50` is `-0.05`, `1000` is
`1`. -/
def thousandths (n : Int) : String :=
  let digits := (toString (n.natAbs % 1000)).toList
  let padded := List.replicate (3 - digits.length) '0' ++ digits
  let kept := (padded.reverse.dropWhile (· == '0')).reverse
  (if n < 0 then "-" else "") ++ toString (n.natAbs / 1000) ++
    (if kept.isEmpty then "" else "." ++ String.ofList kept)

/-- A time of `perMille` thousandths of a step of `step` milliseconds, in milliseconds. It is
written exactly, to a thousandth of a millisecond: a time rounded to a whole millisecond would
give a browser another share of a duration than `Transition.at` reads. -/
def milliseconds (perMille step : Nat) : String := thousandths ((perMille * step : Nat) : Int) ++ "ms"

/-- A time before or after the start of a step, in milliseconds, written exactly. A delay that
is less than nothing starts an animation partway through. -/
def signedMilliseconds (perMille : Int) (step : Nat) : String :=
  thousandths (perMille * step) ++ "ms"

/-- A point of whole counts of `1 / grid` of a user unit, as two numbers of path data. -/
def point (grid : Nat) (p : IVec) : String :=
  thousandths (p.x * 1000 / grid) ++ "," ++ thousandths (p.y * 1000 / grid)

/-- Where a list of segments starts a subpath: at a segment that does not start where the one
before it ended. `last` is where the segment before the list ended, and with none the first
segment starts one. -/
def starts : List ICubic → Option IVec → List Bool
  | [], _ => []
  | c :: rest, last => (last != some c.p0) :: starts rest (some c.p3)

/-- Segments of whole counts as path data, every segment a `C`, with an `M` before each segment
that `marks` says starts a subpath. A segment with no mark starts one. -/
def pathDataWith (grid : Nat) : List ICubic → List Bool → String
  | [], _ => ""
  | c :: rest, marks =>
    (if marks.headD true then "M" ++ point grid c.p0 else "") ++ "C" ++ point grid c.p1 ++ " " ++
      point grid c.p2 ++ " " ++ point grid c.p3 ++ pathDataWith grid rest marks.tail

/-- Segments of whole counts as path data, every segment a `C`, so that two lists of one
length are written with the same commands and a browser can go from one to the other. A
segment that does not start where the one before it ended starts a subpath with `M`. `last` is
where the segment before ended. -/
def pathData (grid : Nat) (segments : List ICubic) (last : Option IVec) : String :=
  pathDataWith grid segments (starts segments last)

end Css

/-- An easing as a CSS easing function. Fewer than two stops are written as two, since
`linear()` takes two at least, and the two stops `0` and `1` are the keyword `linear`. -/
def _root_.Whatwg.Svg.Scene.Easing.css : Easing → String
  | .stops [] => "linear(0, 0)"
  | .stops [v] => "linear(" ++ Css.thousandths v ++ ", " ++ Css.thousandths v ++ ")"
  | .stops [0, 1000] => "linear"
  | .stops values => "linear(" ++ ", ".intercalate (values.map Css.thousandths) ++ ")"
  | .cubic y1 y2 =>
    "cubic-bezier(0.333333, " ++ Css.thousandths y1 ++ ", 0.666667, " ++ Css.thousandths y2 ++ ")"

/-- **A pose as one declaration.** A shift counts in `1 / grid` of a user unit, and is written
to three places. A part revealed is the offset of a dash of two thousand: two thousand less the
part, so that a part past either end of the line is drawn as the whole line or as none of it. -/
def _root_.Whatwg.Svg.Scene.Pose.decl (grid : Nat := 1) : Pose → Css.Decl
  | .shift step =>
    { name := "translate"
      value := Css.thousandths (step.x * 1000 / grid) ++ "px " ++
        Css.thousandths (step.y * 1000 / grid) ++ "px" }
  | .grow size => { name := "scale", value := Css.thousandths size }
  | .reveal part => { name := "stroke-dashoffset", value := toString (2000 - part) }
  | .fade shown => { name := "opacity", value := Css.thousandths shown }
  | .shape segments =>
    { name := "d", value := "path(\"" ++ Css.pathData grid segments none ++ "\")" }

/-- A pose as the text of a CSS declaration. -/
def _root_.Whatwg.Svg.Scene.Pose.css (grid : Nat := 1) (p : Pose) : String := (p.decl grid).css

/-- What a pose needs on its thing beside its own declaration: a size is about the middle of
the thing's own box, and a line that is revealed has one dash of two thousand, twice its
`pathLength`. -/
def _root_.Whatwg.Svg.Scene.Pose.setup : Pose → Css.Decls
  | .grow _ => [("transform-box", "fill-box"), ("transform-origin", "center")]
  | .reveal _ => [("stroke-dasharray", "2000")]
  | _ => []

/-- What a change needs on its thing beside the animation: what its poses need. -/
def _root_.Whatwg.Svg.Scene.Change.setup (c : Change) : Css.Decls := c.start.setup

/-- **The two ends of a change as declarations**: its pose at the start and its pose at the
end. The two ends of a change of shape between lists of one length are written with the same
commands, a subpath started wherever either end starts one, so that a browser goes from one to
the other point by point as `Change.at` does. A subpath started where an outline goes on leaves
the fill of a closed outline as it is. It is seen on a stroke, which then has two ends there
and no join, and on an open line that is filled. -/
def _root_.Whatwg.Svg.Scene.Change.ends (c : Change) (grid : Nat := 1) : Css.Decl × Css.Decl :=
  match c with
  | .morph a b =>
    if a.length = b.length then
      let marks := List.zipWith (· || ·) (Css.starts a none) (Css.starts b none)
      ({ name := "d", value := "path(\"" ++ Css.pathDataWith grid a marks ++ "\")" },
        { name := "d", value := "path(\"" ++ Css.pathDataWith grid b marks ++ "\")" })
    else (c.start.decl grid, c.stop.decl grid)
  | _ => (c.start.decl grid, c.stop.decl grid)

/-- **The rule `@keyframes` of a change under an easing**, under a name: the two ends of the
change, and the easing at the first of them. The easing of a keyframe is that of the way from
it to the next, so it is the easing of the whole animation. -/
def _root_.Whatwg.Svg.Scene.Change.rule (c : Change) (ease : Easing) (name : String)
    (grid : Nat := 1) : Css.Rule :=
  .keyframes name [(c.ends grid).1, ("animation-timing-function", ease.css)] [(c.ends grid).2]

/-- **A frame as declarations**: one for each property that is not at rest, and what those
need beside them, so the still picture writes nothing. A program that reads a moment with
`Motion.frame` writes it so. -/
def _root_.Whatwg.Svg.Scene.Frame.decls (f : Frame) (grid : Nat := 1) : Css.Decls :=
  (f.poses.map fun p => p.decl grid) ++ f.poses.flatMap Pose.setup

/-- A frame as the text of CSS declarations. -/
def _root_.Whatwg.Svg.Scene.Frame.css (f : Frame) (grid : Nat := 1) : String := (f.decls grid).css

/-! ## How a step is played -/

/-- When a reader sees the end of a step at once, with no motion. -/
inductive Reduce where
  /-- Never: the sheet has no rule for it. -/
  | never
  /-- Where the reader asked for reduced motion: the rule stands in
  `@media (prefers-reduced-motion: reduce)`. -/
  | asked
  /-- Always: the rule stands outside any `@media`. A probe shows the effect of the rule so,
  with no setting of the reader's. -/
  | always
  deriving DecidableEq, Repr, Inhabited

/-- **How a step is played.** Every writer of this module takes one, so the sheet and the
things of a step agree. Each field has a default, and a caller names what it changes:
`{ step := 600, stem := "s3" }`. -/
structure Play where
  /-- How long the step is, in milliseconds. A per mille of the default is a millisecond. -/
  step : Nat := 1000
  /-- The stem of the step's names: of its `@keyframes` rules, and of the mark on its things.
  Two steps on one page have two stems. A letter, and then letters, digits and `-`. -/
  stem : String := "m"
  /-- How many counts of a shift or of a shape make one user unit. -/
  grid : Nat := 1
  /-- The moment the step is opened at, in per mille: each delay is that much less. -/
  opened : Nat := 0
  /-- Whether the step stands still at the moment it is opened at. -/
  paused : Bool := false
  /-- A custom property, such as `--t`, that says the moment in place of `opened` wherever an
  ancestor of the thing sets it to a number. With none set, `opened` is the moment. -/
  scrub : Option String := none
  /-- When a reader sees the end of the step at once. -/
  reduce : Reduce := .asked
  deriving DecidableEq, Repr, Inhabited

namespace Play

/-- The step paused, at the moment that a custom property says: one number scrubs it. -/
def scrubbed (play : Play) (property : String := "--t") : Play :=
  { play with scrub := some property, paused := true }

/-- **The declaration that puts a scrubbed step at the moment `t`**, for the `style` of the
picture or of any ancestor of its things. Nothing for a step that no property scrubs. -/
def «at» (play : Play) (t : Nat) : Css.Decls :=
  match play.scrub with
  | some property => [(property, toString t)]
  | none => []

/-- The delay of an animation whose transition starts at `delay` per mille of the step. It is
`opened` less. In a scrubbed step it is a `calc()` of the custom property: the per mille from
the moment to the start of the transition, times the length of a per mille. -/
def delay (play : Play) (delay : Nat) : String :=
  match play.scrub with
  | none => Css.signedMilliseconds ((delay : Int) - play.opened) play.step
  | some property =>
    "calc((" ++ toString delay ++ " - var(" ++ property ++ ", " ++ toString play.opened ++
      ")) * " ++ Css.thousandths play.step ++ "ms)"

/-- Whether the things of the step carry its mark: the step runs, and the sheet has a rule of
reduced motion. A step that stands still is a still picture already. -/
def marked (play : Play) : Bool := !play.paused && play.reduce != .never

/-- **The mark of a step on a thing**: the attribute `data-motion` with the stem. The rule of
reduced motion selects it. It is a custom data attribute, so it joins a thing's own `class` and
replaces none. -/
def mark {t : Tag} (play : Play) : SvgAttr t := .data "motion" play.stem

/-- The selector of the things that carry the step's mark. -/
def selector (play : Play) : String := "[data-motion=\"" ++ play.stem ++ "\"]"

/-- What ends an animation at once: a duration and a delay of nothing. An animation that fills
both ways then shows its end. Both are `!important`, since they must stand over the `style`
attribute that holds the animation. -/
def ended : Css.Decls :=
  [⟨"animation-duration", "0s", true⟩, ⟨"animation-delay", "0s", true⟩]

/-- **The rule of reduced motion**: every animation of a marked thing of the step is over at
once. -/
def reduced (play : Play) : Css.Sheet :=
  match play.reduce with
  | .never => []
  | .asked => [.media "(prefers-reduced-motion: reduce)" [.style play.selector ended]]
  | .always => [.style play.selector ended]

end Play

section

variable {κ : Type}

/-- What the tracks of a motion do, whenever and to whatever they do it: each change with its
easing, once, in the order of their first tracks. The sheet has one rule for each. -/
def _root_.Whatwg.Svg.Scene.Motion.courses (m : Motion κ) : List (Change × Easing) :=
  (m.map fun tr => (tr.change, tr.timing.ease)).eraseDups

/-- The place of the first track of a motion with a change and an easing. -/
def _root_.Whatwg.Svg.Scene.Motion.ruleIndex (m : Motion κ) (c : Change) (ease : Easing) :
    Nat :=
  m.findIdx fun tr => tr.change == c && tr.timing.ease == ease

/-- **The name of the rule of a change under an easing**: the stem, and the place of the first
track with the two. The sheet names the rule so, and so does each animation of such a track. -/
def _root_.Whatwg.Svg.Scene.Motion.ruleName (m : Motion κ) (stem : String) (c : Change)
    (ease : Easing) : String :=
  stem ++ "-" ++ toString (m.ruleIndex c ease)

/-- The text of the rule `@keyframes` of one track, under a name. -/
def _root_.Whatwg.Svg.Scene.Motion.keyframes (name : String) (tr : Track κ) (grid : Nat := 1) :
    String :=
  (tr.change.rule tr.timing.ease name grid).css

/-- One animation of the `animation` property: the name of its rule, the duration, the delay,
and filling both ways. The easing is in the rule. The transition counts in thousandths of the
step. The step is opened at the moment `opened`: the delay is `opened` less, so a track that has
started by then is partway through, and one that is over shows its end. A `paused` animation
stays at that moment. -/
def _root_.Whatwg.Svg.Scene.Motion.animation (name : String) (tr : Track κ) (play : Play := {}) :
    String :=
  name ++ " " ++ Css.milliseconds tr.timing.duration play.step ++ " " ++
    play.delay tr.timing.delay ++ " both" ++ (if play.paused then " paused" else "")

/-- **The rules of a step**: one `@keyframes` rule for each change of the motion under each
easing, named by `Motion.ruleName`, and then the rule of reduced motion where the step has
one. -/
def _root_.Whatwg.Svg.Scene.Motion.rules (m : Motion κ) (play : Play := {}) : Css.Sheet :=
  (m.courses.map fun x => x.1.rule x.2 (m.ruleName play.stem x.1 x.2) play.grid) ++ play.reduced

/-- **The style sheet of a motion**, as text: its rules, one a line. -/
def _root_.Whatwg.Svg.Scene.Motion.sheet (m : Motion κ) (play : Play := {}) : String :=
  (m.rules play).css

/-- **The declarations that a step puts on one thing**: the animations of the tracks with its
key, and what their changes need. None for a key with no track. The step is opened at the
moment `opened`, running or `paused`: a page that is loaded again in the middle of a step goes
on from there, and a paused one is the browser's own still picture of that moment. -/
def _root_.Whatwg.Svg.Scene.Motion.decls [BEq κ] (m : Motion κ) (key : κ) (play : Play := {}) :
    Css.Decls :=
  match m.filter fun tr => tr.key == key with
  | [] => []
  | tracks =>
    { name := "animation"
      value := ", ".intercalate
        (tracks.map fun tr =>
          Motion.animation (m.ruleName play.stem tr.change tr.timing.ease) tr play) } ::
      (tracks.flatMap fun tr => tr.change.setup).eraseDups

/-- **The style of one thing**, as text: its declarations. Nothing for a key with no track. -/
def _root_.Whatwg.Svg.Scene.Motion.style? [BEq κ] (m : Motion κ) (key : κ) (play : Play := {}) :
    Option String :=
  match m.decls key play with
  | [] => none
  | ds => some (Css.Decls.css ds)

/-- Whether a track of the key reveals a line. -/
def _root_.Whatwg.Svg.Scene.Motion.reveals [BEq κ] (m : Motion κ) (key : κ) : Bool :=
  m.any fun tr => tr.key == key &&
    match tr.change with
    | .reveal _ _ => true
    | _ => false

/-- **The declarations of one thing at the moment `t`, with no animation**: each pose of its
tracks, and what they need, each name once. Of two tracks of one property the later is the
one written, as `Motion.frame` reads. A target that draws no animation and a check of a browser
against `Track.at` read a step so. None for a key with no track. -/
def _root_.Whatwg.Svg.Scene.Motion.declsAt [BEq κ] (m : Motion κ) (key : κ) (t : Nat)
    (play : Play := {}) : Css.Decls :=
  match m.filter fun tr => tr.key == key with
  | [] => []
  | tracks =>
    Css.Decls.once ((tracks.map fun tr => (tr.at t).decl play.grid) ++
      (tracks.flatMap fun tr => tr.change.setup).eraseDups)

/-- **The style of one thing at the moment `t`, with no animation**, as text. Nothing for a key
with no track. -/
def _root_.Whatwg.Svg.Scene.Motion.stillStyle? [BEq κ] (m : Motion κ) (key : κ) (t : Nat)
    (play : Play := {}) : Option String :=
  match m.declsAt key t play with
  | [] => none
  | ds => some (Css.Decls.css ds)

end

namespace SvgAttr

variable {t : Tag}

/-- `style`: declarations of CSS, as text. -/
def style (css : String) : SvgAttr t := .attr .style css

/-- `style`: declarations of CSS. -/
def decls (ds : Css.Decls) : SvgAttr t := style ds.css

/-- The `style` attribute of a row of declarations, and no attribute for an empty row. -/
def decls? (ds : Css.Decls) : List (SvgAttr t) := if ds.isEmpty then [] else [decls ds]

/-- `pathLength`: the length that the author counts the path's length as. -/
def pathLength (n : Nat) : SvgAttr t := .attr .pathLength (toString n)

end SvgAttr

/-- **The attributes that put a step on the thing with a key**: `pathLength` of a thousand
where a track reveals it, the step's mark where the sheet has a rule of reduced motion, and one
`style`. The `style` holds the thing's own declarations `own` and the step's, each name once:
where both say a property, the step's stands. A key with no track gets its own `style` and
nothing else, so a still thing is written as it was. -/
def _root_.Whatwg.Svg.Scene.Motion.attrs {κ : Type} [BEq κ] {t : Tag} (m : Motion κ) (key : κ)
    (play : Play := {}) (own : Css.Decls := []) : List (SvgAttr t) :=
  match m.decls key play with
  | [] => SvgAttr.decls? (Css.Decls.once own)
  | ds =>
    (if Motion.reveals m key then [SvgAttr.pathLength 1000] else []) ++
      (if play.marked then [play.mark] else []) ++ SvgAttr.decls? (Css.Decls.merge own ds)

/-- **The attributes that put the poses of a moment on the thing with a key**, with no
animation: `pathLength` where a track reveals it, and one `style` of the thing's own
declarations and its poses. -/
def _root_.Whatwg.Svg.Scene.Motion.attrsAt {κ : Type} [BEq κ] {t : Tag} (m : Motion κ) (key : κ)
    (moment : Nat) (play : Play := {}) (own : Css.Decls := []) : List (SvgAttr t) :=
  (if Motion.reveals m key then [SvgAttr.pathLength 1000] else []) ++
    SvgAttr.decls? (Css.Decls.merge own (m.declsAt key moment play))

/-- **The attributes that put a frame on a thing**: `pathLength` of a thousand where its line is
not whole, and one `style` of the thing's own declarations and the frame's. -/
def _root_.Whatwg.Svg.Scene.Frame.attrs {t : Tag} (f : Frame) (grid : Nat := 1)
    (own : Css.Decls := []) : List (SvgAttr t) :=
  (if f.part = 1000 then [] else [SvgAttr.pathLength 1000]) ++
    SvgAttr.decls? (Css.Decls.merge own (f.decls grid))

/-- `style`: a style sheet as an element of a picture, from its text. -/
def Svg.styleSheet (css : String) : SvgNode := .element .style [] [.text css]

/-- `style`: a style sheet as an element of a picture, from its rules. -/
def Svg.sheet (rules : Css.Sheet) : SvgNode := Svg.styleSheet rules.css

/-- **The sheet of a step as one node**: its rules, and then the caller's own. -/
def _root_.Whatwg.Svg.Scene.Motion.sheetNode {κ : Type} (m : Motion κ) (play : Play := {})
    (more : Css.Sheet := []) : SvgNode :=
  Svg.sheet (m.rules play ++ more)

/-- The centre line of a reveal: a plain white stroke, `cover` wide, with round ends. A track
that reveals it is put on it with `Motion.attrs`, in `more`. -/
def Svg.revealLine (centre : List Cubic) (cover : Rat) (more : List (SvgAttr .path) := [])
    (places : Nat := 3) : SvgNode :=
  Svg.cubics centre
    ([.fill .none, .stroke (.raw "white"), .strokeWidth (.ofRat cover places),
      .strokeLinecap .round] ++ more) places

/-- **A filled outline that is revealed along its centre line.** A stroke of varying width is a
filled outline, and a fill has no dash to draw it by. So the outline is drawn through a mask,
and the mask is the centre line as a plain stroke that a track reveals: where the mask's line
has been drawn, the outline shows. `line` is `Svg.revealLine` of the centre line, at least as
wide as the outline at its widest; for an organic stroke that width is a theorem
(`Stroke.organic_band`). The identifier `id` is written once here, in the mask and in the group
that it masks. -/
def Svg.revealed (id : String) (line : SvgNode) (children : List SvgNode) : List SvgNode :=
  [.element .mask [.ident id, .maskUnits .userSpaceOnUse] [line],
    Svg.g [.attr .mask (urlRef id)] children]

/-! ## Laws -/

section

variable {κ : Type}

/-- A change and an easing are among the courses of a motion exactly when a track of the motion
has the two. -/
theorem _root_.Whatwg.Svg.Scene.Motion.mem_courses {m : Motion κ} {x : Change × Easing} :
    x ∈ m.courses ↔ ∃ tr ∈ m, (tr.change, tr.timing.ease) = x := by
  rw [Motion.courses, List.mem_eraseDups, List.mem_map]

/-- **Every animation names a rule of the sheet.** The rule that a track's animation names is in
the rules of the step, under that name, with the two ends of the track's change and its easing.
So no thing is given an animation that the sheet does not have, and each thing moves by the
easing of its own track. -/
theorem _root_.Whatwg.Svg.Scene.Motion.rule_mem (m : Motion κ) (play : Play) {tr : Track κ}
    (h : tr ∈ m) :
    tr.change.rule tr.timing.ease (m.ruleName play.stem tr.change tr.timing.ease) play.grid ∈
      m.rules play :=
  List.mem_append_left _
    (List.mem_map.mpr ⟨(tr.change, tr.timing.ease), Motion.mem_courses.mpr ⟨tr, h, rfl⟩, rfl⟩)

/-- **Two courses of a motion have two places.** A change and an easing of the motion, and
another change and easing with the same place, are one change and one easing. So no rule of the
sheet stands for two changes, or for one change under two easings. -/
theorem _root_.Whatwg.Svg.Scene.Motion.ruleIndex_inj {m : Motion κ} {c c' : Change}
    {ease ease' : Easing} (h : (c, ease) ∈ m.courses)
    (e : m.ruleIndex c ease = m.ruleIndex c' ease') : c = c' ∧ ease = ease' := by
  obtain ⟨tr, htr, hx⟩ := Motion.mem_courses.mp h
  have hfound : (tr.change == c && tr.timing.ease == ease) = true := by
    rw [← (Prod.mk.inj hx).1, ← (Prod.mk.inj hx).2, beq_self_eq_true, beq_self_eq_true]
    rfl
  have hlt : m.ruleIndex c ease < m.length := List.findIdx_lt_length_of_exists ⟨tr, htr, hfound⟩
  have hlt' : m.ruleIndex c' ease' < m.length := e ▸ hlt
  have h1 : ((m[m.ruleIndex c ease]'hlt).change == c &&
      (m[m.ruleIndex c ease]'hlt).timing.ease == ease) = true :=
    List.findIdx_getElem (p := fun x : Track κ => x.change == c && x.timing.ease == ease)
      (w := hlt)
  have h2 : ((m[m.ruleIndex c' ease']'hlt').change == c' &&
      (m[m.ruleIndex c' ease']'hlt').timing.ease == ease') = true :=
    List.findIdx_getElem (p := fun x : Track κ => x.change == c' && x.timing.ease == ease')
      (w := hlt')
  have same : ∀ (i j : Nat) (hi : i < m.length) (hj : j < m.length), i = j → m[i]'hi = m[j]'hj := by
    intro i j hi hj hij
    subst hij
    rfl
  have hs := same _ _ hlt hlt' e
  have a1 := Bool.and_eq_true_iff.mp h1
  have a2 := Bool.and_eq_true_iff.mp h2
  exact ⟨(beq_iff_eq.mp a1.1).symm.trans ((congrArg Track.change hs).trans (beq_iff_eq.mp a2.1)),
    (beq_iff_eq.mp a1.2).symm.trans
      ((congrArg (fun x : Track κ => x.timing.ease) hs).trans (beq_iff_eq.mp a2.2))⟩

/-- A thing with a track has declarations. -/
theorem _root_.Whatwg.Svg.Scene.Motion.decls_ne_nil [BEq κ] (m : Motion κ) (play : Play) {key : κ}
    {tr : Track κ} (h : tr ∈ m) (hk : (tr.key == key) = true) : m.decls key play ≠ [] := by
  have hm : tr ∈ m.filter fun x => x.key == key := List.mem_filter.mpr ⟨h, hk⟩
  unfold Motion.decls
  split
  · rename_i hnil
    rw [hnil] at hm
    exact nomatch hm
  · exact List.cons_ne_nil _ _

/-- **The rule of reduced motion names every thing that moves.** In a step that carries marks,
each thing with a track is given the mark that the rule selects, whatever its own
declarations. So the rule ends every animation of the step, and a reader who asked for reduced
motion sees no thing of the step move. -/
theorem _root_.Whatwg.Svg.Scene.Motion.mark_mem [BEq κ] {t : Tag} (m : Motion κ) (play : Play)
    (own : Css.Decls) {key : κ} {tr : Track κ} (h : tr ∈ m) (hk : (tr.key == key) = true)
    (hp : play.marked = true) : (play.mark : SvgAttr t) ∈ m.attrs key play own := by
  have hne := Motion.decls_ne_nil m play h hk
  unfold Motion.attrs
  split
  · rename_i hnil
    exact absurd hnil hne
  · rw [if_pos hp]
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

end

end Whatwg.Html
