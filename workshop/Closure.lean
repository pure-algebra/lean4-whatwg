import Lean
import Whatwg.Html.Print.Render
import Whatwg.Html.Content.Valid
import Whatwg.Html.Content.Explain
import Whatwg.Html.Node.SvgBuild
import Whatwg.Html.Node.SvgPaint
import Whatwg.Html.Node.SvgNest
import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Html.Print.Xml
import Whatwg.Svg.Geometry.Stroke
import Whatwg.Svg.Geometry.Shape
import Whatwg.Svg.Geometry.Stack
import Whatwg.Svg.Geometry.Moment
import Whatwg.Svg.Scene.Stage
import Whatwg.Svg.Scene.Frame
import Whatwg.Svg.Scene.Row
import Whatwg.Svg.Scene.Label
import Whatwg.Svg.Scene.Scale
import Whatwg.Svg.Scene.Cross

/-! What a consumer's import of the kit reaches. Run it from the repository root after
`lake build`:

    lake env lean workshop/Closure.lean

It imports the modules that lean4-effect4's view imports or will import (the HTML checker and
printer, the picture writer, the geometry of strokes and the scene), and prints how many modules
of this repository their import closure holds, and every module of it that is not Lean's own and
not this repository's. The Effect4 coordinator asked that the definitions a consumer imports
reach Lean alone (`docs/research/2026-10-12-svg-seat-guidance-4.md`): the second line must then
be empty. No module imports this file, and no gate reads its output. -/

open Lean Elab Command in
run_cmd do
  let names := (← getEnv).header.moduleNames
  let ours := names.filter fun n => n.getRoot == `Whatwg
  let own : List Name := [`Lean, `Init, `Std, `Whatwg]
  let outside := names.filter fun n => !own.contains n.getRoot
  let auto := names.filter fun n => (`Whatwg.Auto).isPrefixOf n
  logInfo m!"{names.size} modules in the closure, {ours.size} of them of this repository"
  logInfo m!"outside Lean and this repository: {outside.size} ({(outside.map fun n => n.getRoot).toList.eraseDups})"
  logInfo m!"proof-search modules of this repository in the closure: {auto}"
