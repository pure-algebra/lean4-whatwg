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

- `Step.nodes s play draw`: the inline way, the style sheet of the step's tracks, and then each
  thing drawn, with its motion on it. The things are those drawn at the moment the step is
  opened at: the things that leave too, until the step's end. A step that a property scrubs
  draws them all, since any moment may be asked of it.
- `Step.still s t play draw`: the things drawn at the moment `t`, each with its pose written as
  plain declarations and no animation. A target that plays no animation, and a check of a
  browser against the kit's reading, draw a step so.
- `Step.sheet s play`: the rules of the step, as rules of the tree of CSS
  (`Whatwg/Html/Node/Css.lean`; the one tree since slice S22). `Step.things s play draw`: the
  things drawn, with no sheet. `Step.nodes` is the two together the inline way.

A page may refuse what is inline: a `style` element and a `style` attribute. With
`reach := .sheet` in the `Play`, a step is written with neither (the consumer's ask W11 of
`docs/research/2026-10-12-whatwg-requests.md`). `Step.nodes` is then the things alone, each
with its name and no `style`, and the caller writes `Step.sheet` to a file that the page
links. The rules of several steps go in one file, one after another, and their stems keep them
apart:

```
let p := { step := 600, stem := "s3", reach := .sheet }
Svg.svg [] (s.nodes p draw)                                   -- no `style` in it
(s.sheet p ++ s'.sheet { p with stem := "s4" }).css           -- the text of the file
```

`Step.stillSheet s t play` is the same for a moment with no animation.

`draw` is given a thing and its motion as attributes for whatever tag it puts them on: a group
around the thing, or the thing's own element. A line that a track reveals takes them on the
path itself, since `pathLength` is an attribute of a path. A thing that already has a
`transform` attribute takes them on a group around it: the box that a change of size reads
would otherwise move the origin of that attribute too.

What this module does not claim: anything about what a browser draws. The laws of a step are
about its tracks and its frames (`Whatwg/Svg/Scene/Step/Laws.lean`), and
`docs/research/2026-10-12-motion-probe/README.md` records what one browser computed from them.
Nor that the markup of a step by the sheet holds no `style`: the step gives none
(`Motion.attrs_no_style`, `Step.nodes_sheet`), and what `draw` writes of its own is the
caller's.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Scene (Step Motion)

/-- The motion of one thing, as attributes for whatever tag it is put on. -/
abbrev Svg.Moving : Type := (t : Tag) → List (SvgAttr t)

section

variable {α κ : Type} [BEq κ]

/-- **The things of a step as nodes**, each drawn with its motion, and no sheet. A thing with
no track is given no attribute, so it is written as a still picture writes it. -/
def _root_.Whatwg.Svg.Scene.Step.things (s : Step α κ) (play : Play)
    (draw : α → Svg.Moving → SvgNode) : List SvgNode :=
  let m := s.motion
  let t := if play.scrub.isSome then 0 else play.opened
  (s.drawn t).map fun a => draw a fun _ => Motion.attrs m (s.key a) play

/-- **The rules of a step**, and then the caller's own. By the sheet they are the text of a
file: the `@keyframes` rules, the rule of each thing that moves, and the rule of reduced
motion. The rules of two steps of one page go in one file one after the other, each step with
its own stem. -/
def _root_.Whatwg.Svg.Scene.Step.sheet (s : Step α κ) (play : Play) (more : Css.Sheet := []) :
    Css.Sheet :=
  s.motion.rules play ++ more

/-- **A step as nodes.** The inline way: the style sheet of its tracks and the caller's own
rules, and then each thing drawn, with its motion. By the sheet: the things alone, and no
`style` element; the caller writes `Step.sheet` where the page links it. -/
def _root_.Whatwg.Svg.Scene.Step.nodes (s : Step α κ) (play : Play)
    (draw : α → Svg.Moving → SvgNode) (more : Css.Sheet := []) : List SvgNode :=
  if play.reach = .sheet then s.things play draw
  else Svg.sheet (s.sheet play more) :: s.things play draw

/-- **A moment of a step as nodes, with no animation**: each thing drawn at the moment `t`, with
its pose then as plain declarations. -/
def _root_.Whatwg.Svg.Scene.Step.still (s : Step α κ) (t : Nat) (play : Play)
    (draw : α → Svg.Moving → SvgNode) : List SvgNode :=
  let m := s.motion
  (s.drawn t).map fun a => draw a fun _ => Motion.attrsAt m (s.key a) t play

/-- **The rules of a moment of a step, with no animation**, and then the caller's own: by the
sheet, the rule of each thing with its pose then. -/
def _root_.Whatwg.Svg.Scene.Step.stillSheet (s : Step α κ) (t : Nat) (play : Play)
    (more : Css.Sheet := []) : Css.Sheet :=
  s.motion.rulesAt t play ++ more

/-- The things of a step are one node for each thing drawn. -/
theorem _root_.Whatwg.Svg.Scene.Step.length_things (s : Step α κ) (play : Play)
    (draw : α → Svg.Moving → SvgNode) :
    (s.things play draw).length =
      (s.drawn (if play.scrub.isSome then 0 else play.opened)).length := by
  simp only [Step.things, List.length_map]

/-- The inline way a step is its sheet as one node, and then its things. -/
theorem _root_.Whatwg.Svg.Scene.Step.nodes_inline (s : Step α κ) (play : Play)
    (draw : α → Svg.Moving → SvgNode) (more : Css.Sheet) (h : play.reach = .inline) :
    s.nodes play draw more = Svg.sheet (s.sheet play more) :: s.things play draw := by
  have hn : ¬ play.reach = Reach.sheet := by
    rw [h]
    decide
  unfold Step.nodes
  rw [if_neg hn]

/-- **By the sheet a step is its things, and no sheet stands among its nodes.** -/
theorem _root_.Whatwg.Svg.Scene.Step.nodes_sheet (s : Step α κ) (play : Play)
    (draw : α → Svg.Moving → SvgNode) (more : Css.Sheet) (h : play.reach = .sheet) :
    s.nodes play draw more = s.things play draw := by
  unfold Step.nodes
  rw [if_pos h]

/-- The inline way a step is written as one sheet and one node for each thing drawn. -/
theorem _root_.Whatwg.Svg.Scene.Step.length_nodes (s : Step α κ) (play : Play)
    (draw : α → Svg.Moving → SvgNode) (more : Css.Sheet) (h : play.reach = .inline) :
    (s.nodes play draw more).length =
      (s.drawn (if play.scrub.isSome then 0 else play.opened)).length + 1 := by
  rw [Step.nodes_inline s play draw more h, List.length_cons, Step.length_things]

/-- A moment of a step is written as one node for each thing drawn then. -/
theorem _root_.Whatwg.Svg.Scene.Step.length_still (s : Step α κ) (t : Nat) (play : Play)
    (draw : α → Svg.Moving → SvgNode) : (s.still t play draw).length = (s.drawn t).length := by
  simp only [Step.still, List.length_map]

end

end Whatwg.Html