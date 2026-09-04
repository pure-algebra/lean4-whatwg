import Whatwg.Html.Content.Transparent

/-!
# WhatwgTest.Html.Lattice

Probes of the lattice and transparency theorems over the schema generated
from the standard (slice H6.1): the quantified statements are in
`Whatwg.Html.Content.Lattice` and `Whatwg.Html.Content.Transparent`; the
points below are what they say at named sets and tags. Finite probes.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Lattice

open Whatwg.Html.Schema
open Whatwg.Html.Content

/-! ## Derived sets are inside their parents -/

example : ContentSet.parent? .flow_without_interactive_noscript = some .flow_without_interactive := by decide
example : SubsetOf Sets.flow_without_interactive_noscript Sets.flow_without_interactive :=
  parent_subset .flow_without_interactive_noscript .flow_without_interactive (by decide)
example : ContentSet.parent? .flow = none := by decide

/-! ## Categories -/

example : Sets.flow .div = true ∧ Sets.phrasing .div = false := by decide
example : Sets.phrasing .em = true ∧ Sets.flow .em = true := by decide
example : Cats.interactive .button = true ∧ Cats.interactive .a = true := by decide
example : Sets.flow_without_interactive .button = false := by decide
example : Sets.flow .style = false ∧ Sets.metadata .style = true := by decide
example : Sets.only_li .script = true ∧ Sets.only_li .p = false := by decide
example : Sets.phrasing_without_dfn .embed = true := by decide
example : Sets.nothing .pcdata = false ∧ Sets.text .pcdata = true := by decide

/-! ## Transparency -/

example : ContentSet.transparentPayload .flow .a = some .flow_without_interactive := by decide
example : ContentSet.transparentPayload .phrasing .a = some .phrasing_without_interactive := by decide
example : ContentSet.transparentPayload .flow .video = some .flow_without_media := by decide
example : ContentSet.transparentPayload .flow .div = none := by decide
example : ContentSet.transparentPayload .metadata .noscript = some .only_link_style_meta_strict := by decide
example : isTransparentTag .a = true ∧ isTransparentTag .div = false := by decide

/-! ## The resolver -/

example : resolveChildSet .div .flow = some .flow := by decide
example : resolveChildSet .a .phrasing = some .phrasing_without_interactive := by decide
example : resolveChildSet .br .flow = some .nothing := by decide
example : resolveChildSet .pcdata .flow = none := by decide

end WhatwgTest.Html.Lattice
