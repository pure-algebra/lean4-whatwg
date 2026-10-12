import Whatwg.Html.Node.SvgDraw
import Whatwg.Svg.Scene.Motion

/-!
# Whatwg.Html.Node.SvgMotion

Owner: the motion of a step as CSS (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-65).

`Whatwg/Svg/Scene/Motion.lean` has the motion of a step as data: a list of tracks, each a key,
a change and a transition. A program that draws every moment itself reads a track with
`Track.at`. A browser can draw the moments: this module writes the same tracks as CSS
animations, so a step is one picture and its tracks, and no row of pictures.

```
let m := (Motion.arrive key place j move enter ++ Motion.depart key j leave).within
Svg.svg [] (Svg.styleSheet m.sheet :: marks)       -- one `@keyframes` rule for each track
Svg.path d (m.attrs k 600)                         -- the thing with the key `k`, in a step of 600 ms
```

What is written, for the track at the place `i` of the list, with the name `m` and `i`:

- `@keyframes mi { from { … } to { … } }`, the two poses of its change. A shift is the
  property `translate`, a size is `scale`, an opacity is `opacity`, and a part revealed is
  `stroke-dashoffset` of a line whose `pathLength` is a thousand.
- on the thing itself, `animation: mi <duration> <easing> <delay> both`. Filling both ways
  shows the start until the delay is over and the end afterwards, as `Transition.at` reads.
- the easing: `Easing.stops` as `linear(…)`, and `Easing.cubic y1 y2` as
  `cubic-bezier(0.333333, y1, 0.666667, y2)`.

`translate` and `scale` are properties of their own in CSS Transforms 2, so a shift and a size
on one thing do not replace each other, and neither replaces a `transform` attribute.

What this module does not claim. The text is written by rule and read back by nothing: no
grammar of CSS is sealed in this repository, so no gate judges it (debt D119). A browser
computes in floating point; it reads `1/3` at six places; and between two stops of `linear()`
it draws the straight line that `Easing.stopsAt` rounds down. Two tracks of one kind on one key
write one property twice, and the later one wins.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Value (Cubic)
open Whatwg.Svg.Scene (IVec Easing Transition Pose Change Track Motion)

namespace Css

/-- A count of thousandths as a CSS number: `1567` is `1.567`, `-50` is `-0.05`, `1000` is
`1`. -/
def thousandths (n : Int) : String :=
  let digits := (toString (n.natAbs % 1000)).toList
  let padded := List.replicate (3 - digits.length) '0' ++ digits
  let kept := (padded.reverse.dropWhile (· == '0')).reverse
  (if n < 0 then "-" else "") ++ toString (n.natAbs / 1000) ++
    (if kept.isEmpty then "" else "." ++ String.ofList kept)

/-- A time of `perMille` thousandths of a step of `step` milliseconds, in milliseconds. -/
def milliseconds (perMille step : Nat) : String := toString (perMille * step / 1000) ++ "ms"

end Css

/-- An easing as a CSS easing function. Fewer than two stops are written as two, since
`linear()` takes two at least. -/
def _root_.Whatwg.Svg.Scene.Easing.css : Easing → String
  | .stops [] => "linear(0, 0)"
  | .stops [v] => "linear(" ++ Css.thousandths v ++ ", " ++ Css.thousandths v ++ ")"
  | .stops values => "linear(" ++ ", ".intercalate (values.map Css.thousandths) ++ ")"
  | .cubic y1 y2 =>
    "cubic-bezier(0.333333, " ++ Css.thousandths y1 ++ ", 0.666667, " ++ Css.thousandths y2 ++ ")"

/-- A pose as a CSS declaration. A shift counts in `1 / grid` of a user unit, and is written to
three places. -/
def _root_.Whatwg.Svg.Scene.Pose.css (grid : Nat := 1) : Pose → String
  | .shift step =>
    "translate: " ++ Css.thousandths (step.x * 1000 / grid) ++ "px " ++
      Css.thousandths (step.y * 1000 / grid) ++ "px"
  | .grow size => "scale: " ++ Css.thousandths size
  | .reveal part => "stroke-dashoffset: " ++ toString (1000 - part)
  | .fade shown => "opacity: " ++ Css.thousandths shown

namespace Motion

variable {κ : Type}

/-- The rule `@keyframes` of one track, under a name. -/
def keyframes (name : String) (tr : Track κ) (grid : Nat := 1) : String :=
  "@keyframes " ++ name ++ " { from { " ++ tr.change.start.css grid ++ " } to { " ++
    tr.change.stop.css grid ++ " } }"

/-- One animation of the `animation` property: the name, the duration, the easing, the delay,
and filling both ways. The transition counts in thousandths of a step of `step`
milliseconds. -/
def animation (name : String) (tr : Track κ) (step : Nat) : String :=
  name ++ " " ++ Css.milliseconds tr.timing.duration step ++ " " ++ tr.timing.ease.css ++ " " ++
    Css.milliseconds tr.timing.delay step ++ " both"

/-- **The style sheet of a motion**: one `@keyframes` rule for each track, named by the track's
place in the list after `stem`. -/
def sheet (m : Motion κ) (grid : Nat := 1) (stem : String := "m") : String :=
  "\n".intercalate (m.zipIdx.map fun p => keyframes (stem ++ toString p.2) p.1 grid)

/-- What a change needs on its thing beside the animation: a size grows about the middle of
the thing's own box, and a line that is revealed has one dash as long as itself. -/
def setup : Change → String
  | .grow _ _ => " transform-box: fill-box; transform-origin: center;"
  | .reveal _ _ => " stroke-dasharray: 1000;"
  | _ => ""

/-- **The style of one thing**: the animations of the tracks with its key, and what they need.
Nothing for a key with no track. -/
def style? [BEq κ] (m : Motion κ) (key : κ) (step : Nat) (stem : String := "m") : Option String :=
  match m.zipIdx.filter fun p => p.1.key == key with
  | [] => none
  | tracks =>
    some ("animation: " ++
      ", ".intercalate (tracks.map fun p => animation (stem ++ toString p.2) p.1 step) ++ ";" ++
      String.join ((tracks.map fun p => setup p.1.change).eraseDups))

/-- Whether a track of the key reveals a line. -/
def reveals [BEq κ] (m : Motion κ) (key : κ) : Bool :=
  m.any fun tr => tr.key == key &&
    match tr.change with
    | .reveal _ _ => true
    | _ => false

end Motion

namespace SvgAttr

variable {t : Tag}

/-- `style`: declarations of CSS. -/
def style (css : String) : SvgAttr t := .attr .style css

/-- `pathLength`: the length that the author counts the path's length as. -/
def pathLength (n : Nat) : SvgAttr t := .attr .pathLength (toString n)

end SvgAttr

/-- **The attributes that put a motion on the thing with a key**, in a step of `step`
milliseconds: its `style`, and `pathLength` of a thousand where a track reveals it. Nothing for
a key with no track, so a still thing is written as it was. -/
def Motion.attrs {κ : Type} [BEq κ] {t : Tag} (m : Motion κ) (key : κ) (step : Nat)
    (stem : String := "m") : List (SvgAttr t) :=
  match Motion.style? m key step stem with
  | none => []
  | some css =>
    (if Motion.reveals m key then [SvgAttr.pathLength 1000] else []) ++ [SvgAttr.style css]

/-- **The style of one thing at the moment `t`, with no animation**: each pose of its tracks as
a declaration. A target that draws no animation, a reader who asked for reduced motion, and a
check of a browser against `Track.at` all read a step so. Nothing for a key with no track. -/
def Motion.stillStyle? {κ : Type} [BEq κ] (m : Motion κ) (key : κ) (t : Nat) (grid : Nat := 1) :
    Option String :=
  match m.filter fun tr => tr.key == key with
  | [] => none
  | tracks =>
    some ("; ".intercalate (tracks.map fun tr => (tr.at t).css grid) ++ ";" ++
      String.join ((tracks.map fun tr => Motion.setup tr.change).eraseDups))

/-- The attributes that put the poses of the moment `t` on the thing with a key. -/
def Motion.attrsAt {κ : Type} [BEq κ] {t : Tag} (m : Motion κ) (key : κ) (moment : Nat)
    (grid : Nat := 1) : List (SvgAttr t) :=
  match Motion.stillStyle? m key moment grid with
  | none => []
  | some css =>
    (if Motion.reveals m key then [SvgAttr.pathLength 1000] else []) ++ [SvgAttr.style css]

/-- `style`: a style sheet as an element of a picture. -/
def Svg.styleSheet (css : String) : SvgNode := .element .style [] [.text css]

/-- The centre line of a reveal: a plain white stroke, `cover` wide, with round ends. A track
that reveals it is put on it with `Motion.attrs`, in `more`. -/
def Svg.revealLine (centre : List Cubic) (cover : Rat) (more : List (SvgAttr .path) := [])
    (places : Nat := 3) : SvgNode :=
  Svg.cubics centre
    ([.fill .none, .stroke (.raw "white"), .strokeWidth (.ofRat cover places),
      .attr .stroke_linecap "round"] ++ more) places

/-- **A filled outline that is revealed along its centre line.** A stroke of varying width is a
filled outline, and a fill has no dash to draw it by. So the outline is drawn through a mask,
and the mask is the centre line as a plain stroke that a track reveals: where the mask's line
has been drawn, the outline shows. `line` is `Svg.revealLine` of the centre line, at least as
wide as the outline at its widest; for an organic stroke that width is a theorem
(`Stroke.organic_band`). The identifier `id` is written once here, in the mask and in the group
that it masks. -/
def Svg.revealed (id : String) (line : SvgNode) (children : List SvgNode) : List SvgNode :=
  [.element .mask [.ident id, .attr .maskUnits "userSpaceOnUse"] [line],
    Svg.g [.attr .mask (urlRef id)] children]

end Whatwg.Html
