import Whatwg.Html.Node.Typed

/-!
# Whatwg.Html.Node.Evidence

The shape `html!` (slice H5) builds: an element from a raw literal and a
proof that the literal's children are valid, `Element.ofRaw`. The proof is
a proposition, erased by the compiler, and `html!` assembles it from
`Content.validAll_cons` and `Element.valid` step by step, so the kernel
checks each node once against the literal and never re-evaluates a
subtree.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag Attr)
open Whatwg.Html.Content (Ctx validAll attrsOk)

/-- An element from its raw children and the proofs. -/
def Element.ofRaw {t : Tag} {ctx : Ctx} (attrs : List AttrVal) (children : List RawNode)
    (ha : attrsOk t (rawAttrs attrs) = true) (hs : Content.seqOk (ctx.child t) t children = true)
    (hc : validAll (ctx.child t) children = true) (ht : t.markupName.isSome = true) : Element t ctx :=
  ⟨attrs, children, ha, hs, hc, ht⟩

/-- The erasure of `Element.ofRaw` is the raw element it was built from. -/
theorem Element.ofRaw_toRaw {t : Tag} {ctx : Ctx} (attrs : List AttrVal) (children : List RawNode)
    (ha : attrsOk t (rawAttrs attrs) = true) (hs : Content.seqOk (ctx.child t) t children = true)
    (hc : validAll (ctx.child t) children = true) (ht : t.markupName.isSome = true) :
    (Element.ofRaw attrs children ha hs hc ht).toRaw = .element t.markupText (rawAttrs attrs) children :=
  rfl

end Whatwg.Html
