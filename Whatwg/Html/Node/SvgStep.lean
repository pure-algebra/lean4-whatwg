import Whatwg.Html.Node.SvgMotion
import Whatwg.Svg.Scene.Step

/-!
# Whatwg.Html.Node.SvgStep

Owner: a step as nodes of a picture (slice S17 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-95).

`Whatwg/Svg/Scene/Step.lean` has a step as one value: its key, its two pictures and its plan.
`Whatwg/Html/Node/SvgMotion.lean` writes a motion as CSS, played as a `Play` says. This module
puts the two together, so that a program that draws a step writes how one thing is drawn and
nothing else:

```
s.nodes { step := 600 } fun item motion => boxNode item (motion .g)
```

- `Step.nodes s play draw`: the style sheet of the step's tracks, and then each thing drawn, with
  its motion on it. The things are those drawn at the moment the step is opened at: the things
  that leave too, until the step's end. A step that a property scrubs draws them all, since
  any moment may be asked of it.
- `Step.still s t play draw`: the things drawn at the moment `t`, each with its pose written as
  plain declarations and no animation. A target that plays no animation, and a check of a
  browser against the kit's reading, draw a step so.

`draw` is given a thing and its motion as attributes for whatever tag it puts them on: a group
around the thing, or the thing's own element. A line that a track reveals takes them on the
path itself, since `pathLength` is an attribute of a path. A thing that already has a
`transform` attribute takes them on a group around it: the box that a change of size reads
would otherwise move the origin of that attribute too.

What this module does not claim: anything about what a browser draws. The laws of a step are
about its tracks and its frames (`Whatwg/Svg/Scene/Step/Laws.lean`), and
`docs/research/2026-10-12-motion-probe/README.md` records what one browser computed from them.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Scene (Step Motion)

/-- The motion of one thing, as attributes for whatever tag it is put on. -/
abbrev Svg.Moving : Type := (t : Tag) → List (SvgAttr t)

section

variable {α κ : Type} [BEq κ]

/-- **A step as nodes**: the style sheet of its tracks and the caller's own rules, and then each
thing drawn, with its motion. A thing with no track is given no attribute, so it is written as
a still picture writes it. -/
def _root_.Whatwg.Svg.Scene.Step.nodes (s : Step α κ) (play : Play)
    (draw : α → Svg.Moving → SvgNode) (more : Css.Sheet := []) : List SvgNode :=
  let m := s.motion
  let t := if play.scrub.isSome then 0 else play.opened
  m.sheetNode play more :: (s.drawn t).map fun a => draw a fun _ => Motion.attrs m (s.key a) play

/-- **A moment of a step as nodes, with no animation**: each thing drawn at the moment `t`, with
its pose then as plain declarations. -/
def _root_.Whatwg.Svg.Scene.Step.still (s : Step α κ) (t : Nat) (play : Play)
    (draw : α → Svg.Moving → SvgNode) : List SvgNode :=
  let m := s.motion
  (s.drawn t).map fun a => draw a fun _ => Motion.attrsAt m (s.key a) t play

/-- A step is written as one sheet and one node for each thing drawn. -/
theorem _root_.Whatwg.Svg.Scene.Step.length_nodes (s : Step α κ) (play : Play)
    (draw : α → Svg.Moving → SvgNode) (more : Css.Sheet) :
    (s.nodes play draw more).length =
      (s.drawn (if play.scrub.isSome then 0 else play.opened)).length + 1 := by
  simp only [Step.nodes, List.length_cons, List.length_map]

/-- A moment of a step is written as one node for each thing drawn then. -/
theorem _root_.Whatwg.Svg.Scene.Step.length_still (s : Step α κ) (t : Nat) (play : Play)
    (draw : α → Svg.Moving → SvgNode) : (s.still t play draw).length = (s.drawn t).length := by
  simp only [Step.still, List.length_map]

end

end Whatwg.Html