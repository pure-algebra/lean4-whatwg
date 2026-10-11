import Whatwg.Html.Content.Valid

/-!
# WhatwgTest.Html.Lattice

Probes of the categories, bases, contexts and the checker (slice H7): the
quantified statements are in `Whatwg.Html.Content.{Lattice,Context,Valid}`;
the points below are what they say at named tags and positions. Finite
probes.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Lattice

open Whatwg.Html.Schema
open Whatwg.Html.Content
open Whatwg.Html (RawNode)

/-! ## Categories and bases -/

example : Bases.flow .div = true ∧ Bases.phrasing .div = false := by decide
example : Bases.phrasing .em = true ∧ Bases.flow .em = true := by decide
example : Cats.interactive .button = true ∧ Cats.interactive .a = true := by decide
example : Bases.flow .style = false ∧ Bases.metadata .style = true := by decide
example : Bases.only_li .script = true ∧ Bases.only_li .p = false := by decide
example : Bases.nothing .pcdata = false ∧ Bases.text .pcdata = true := by decide
example : Tag.ownExcl .a = { interactive := true, a := true } := by decide
example : Tag.ownExcl .header = { header := true, footer := true } := by decide
example : Tag.isTransparent .a = true ∧ Tag.isTransparent .div = false := by decide

/-! ## Contexts -/

example : Ctx.admits Ctx.flow .div = true := by decide
example : Ctx.admits Ctx.phrasing .div = false := by decide
example : Ctx.admits (Ctx.child Ctx.flow .a) .button = false := by decide
example : Ctx.admits (Ctx.child Ctx.flow .a) .div = true := by decide
example : Ctx.admits (Ctx.child (Ctx.child Ctx.phrasing .dfn) .span) .dfn = false := by decide
example : Ctx.admits (Ctx.child Ctx.flow .video) .source = true := by decide
example : Ctx.admits (Ctx.child Ctx.flow .br) .pcdata = false := by decide
example : (Ctx.child Ctx.metadata .noscript).base = .only_link_style_meta_strict := by decide
-- The prose of a context, by evaluation (`String.intercalate` does not reduce
-- under `decide`).
#guard Ctx.describe (Ctx.child Ctx.phrasing .a) == "phrasing, excluding interactive content, a"

/-! ## Attribute conditions -/

example : Tag.interactiveIf .a = some (.hasAny ["href"]) := by decide
example : Tag.interactiveIf .input = some (.attrNot "type" "hidden") := by decide
example : Ctx.interactiveWith .a [] = false ∧ Ctx.interactiveWith .a [("href", "/")] = true := by decide
example : Ctx.interactiveWith .input [("type", "Hidden")] = false := by decide
example : Ctx.interactiveWith .button [] = true := by decide
example : validIn Ctx.flow (.element "button" [] [.element "a" [] [.text "x"]]) = true := by decide +kernel
example : validIn Ctx.flow (.element "button" [] [.element "a" [("href", "/")] [.text "x"]]) = false := by decide +kernel

/-! ## Sequences -/

example : Seq.accepts Bases.flow (.seq (.tag .head) (.tag .body)) [.head, .body] = true := by decide
example : Seq.accepts Bases.flow (.seq (.tag .head) (.tag .body)) [.body, .head] = false := by decide
example : seqOk (Ctx.child Ctx.document .html) .html [.element "head" [] [], .element "body" [] []] = true := by decide +kernel
example : seqOk (Ctx.child Ctx.flow .table) .table [.element "caption" [] [], .element "tr" [] [], .element "script" [] []] = true := by decide +kernel
example : seqOk (Ctx.child Ctx.flow .table) .table [.element "tfoot" [] [], .element "tr" [] []] = false := by decide +kernel
example : seqOk (Ctx.child Ctx.flow .div) .div [.element "p" [] []] = true := by decide

/-! ## The checker -/

example : validIn Ctx.flow (.element "p" [] [.text "x", .element "em" [] [.text "y"]]) = true := by decide +kernel
example : validIn Ctx.flow (.element "p" [] [.element "div" [] []]) = false := by decide +kernel
example : validIn Ctx.phrasing (.element "dfn" [] [.element "span" [] [.element "dfn" [] []]]) = false := by decide +kernel
example : validIn Ctx.flow (.element "div" [("class", "x"), ("data-role", "y")] []) = true := by decide +kernel
example : validIn Ctx.flow (.element "div" [("href", "x")] []) = false := by decide +kernel
example : validIn Ctx.flow (.element "div" [("id", "a"), ("id", "b")] []) = false := by decide +kernel
example : validIn Ctx.flow (.element "blink" [] []) = false := by decide +kernel
example : validIn Ctx.flow (.element "br" [] [.comment "x"]) = false := by decide +kernel
example : validIn Ctx.document (.element "html" [] [.element "head" [] [.element "title" [] [.text "t"]], .element "body" [] []]) = true := by decide +kernel

end WhatwgTest.Html.Lattice
