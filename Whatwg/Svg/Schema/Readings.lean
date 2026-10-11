/-!
# Whatwg.Svg.Schema.Readings

Owner: the readings of the content models that the SVG 2 definitions state as a sentence
(ruling SV-4 of `docs/SVG-PACKAGE-PLAN.md`). The definitions give 59 content models by a kind
and four by a sentence. A person reads each sentence once, here, as first-order data.
`WhatwgGates/SvgDefinitionsEmit.lean` imports this module and writes each reading into the
generated `Whatwg.Svg.Schema.ContentModel`.

Each reading carries the sentence it reads and the SHA-256 of the entry that holds it, as
`generated/svg-elements.tsv` records both. The gate refuses a reading whose sentence or digest
is not the entry's: when the pin moves and an entry changes, its sentence is read again.

The names in a reading are the definitions' own: an element name, or an element category's
name. This module states no law. It does not say that a reading is the only one a sentence
bears: the two bounds below are the seat's reading of "exactly one" and "at most one".
-/

namespace Whatwg.Svg.Schema.Readings

/-- A bound that a sentence states: among an element's children, the members of `categories`
and the elements of `elements` together number at least `atLeast` and at most `atMost`. -/
structure Bound where
  categories : List String := []
  elements : List String := []
  atLeast : Nat
  atMost : Nat

/-- The reading of one sentence. The children are the members of `categories` and the
`elements`. With `inherits`, the parent's content model applies as well, and a parent in
`through` hands on its own parent's model. `excluded` names elements the sentence excludes. -/
structure Reading where
  element : String
  digest : String
  sentence : String
  categories : List String := []
  elements : List String := []
  inherits : Bool := false
  through : List String := []
  excluded : List String := []
  bounds : List Bound := []

/-- The four sentences of the pin, each read once. -/
def readings : List Reading :=
  [{ element := "a"
     digest := "a43c69d274ed97b26f5256ca865c607f715fb65b152801bf15eb9f97d223a92b"
     sentence := "Descriptive content, plus any element or text allowed by its parent's content model, except for another a element. If the parent is a switch element, use the content model of the nearest ancestor that isn't a switch."
     categories := ["descriptive"]
     inherits := true
     through := ["switch"]
     excluded := ["a"] },
   { element := "feDiffuseLighting"
     digest := "e2a88fa483e133516cf121bdc3dc071b6010543e03ea92ed2bb06802811056bb"
     sentence := "Any number of descriptive elements, 'script' and exactly one light source element, in any order."
     categories := ["descriptive", "light source"]
     elements := ["script"]
     bounds := [{ categories := ["light source"], atLeast := 1, atMost := 1 }] },
   { element := "feSpecularLighting"
     digest := "392d59c7b82de98607d61bda2af14d340abb979b52b0876d75f132abf89fb305"
     sentence := "Any number of descriptive elements, 'script' and exactly one light source element, in any order."
     categories := ["descriptive", "light source"]
     elements := ["script"]
     bounds := [{ categories := ["light source"], atLeast := 1, atMost := 1 }] },
   { element := "animateMotion"
     digest := "a0ec60c60ee1466fd916938f5b751d354ae396a724b120ac8d05256cdf331fef"
     sentence := "Any number of descriptive elements, 'script' and at most one 'mpath' element, in any order."
     categories := ["descriptive"]
     elements := ["script", "mpath"]
     bounds := [{ elements := ["mpath"], atLeast := 0, atMost := 1 }] }]

end Whatwg.Svg.Schema.Readings
