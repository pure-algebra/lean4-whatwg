/-!
# Whatwg.Html.Schema.Exclusions

The descendant exclusions of the HTML Standard's content models, as a
record of flags (ruling HP-13): four categories (interactive content, media
elements, heading content, sectioning content) and eleven elements. A
context carries the union of the exclusions of every ancestor, so "no
`dfn` element descendants" holds through any depth, and a transparent
element inherits its context's base and adds its own exclusions. A record
rather than a list so that equal exclusions are one value and a context
literal in a type is canonical.
-/

namespace Whatwg.Html.Schema

/-- The exclusion flags. Every field defaults to `false`. -/
structure Exclusions where
  interactive : Bool := false
  media : Bool := false
  heading : Bool := false
  sectioning : Bool := false
  noscript : Bool := false
  dfn : Bool := false
  meter : Bool := false
  progress : Bool := false
  label : Bool := false
  form : Bool := false
  table : Bool := false
  header : Bool := false
  footer : Bool := false
  address : Bool := false
  a : Bool := false
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Exclusions

/-- No exclusions. -/
def none : Exclusions := {}

/-- The union, field by field. -/
def union (x y : Exclusions) : Exclusions :=
  { interactive := x.interactive || y.interactive, media := x.media || y.media,
    heading := x.heading || y.heading, sectioning := x.sectioning || y.sectioning,
    noscript := x.noscript || y.noscript, dfn := x.dfn || y.dfn, meter := x.meter || y.meter,
    progress := x.progress || y.progress, label := x.label || y.label, form := x.form || y.form,
    table := x.table || y.table, header := x.header || y.header, footer := x.footer || y.footer,
    address := x.address || y.address, a := x.a || y.a }

/-- The flags as a list, in field order: the form the lemmas reason in. -/
def flags (x : Exclusions) : List Bool :=
  [x.interactive, x.media, x.heading, x.sectioning, x.noscript, x.dfn, x.meter, x.progress,
   x.label, x.form, x.table, x.header, x.footer, x.address, x.a]

/-- `x ⊆ y`: every flag of `x` is a flag of `y`. -/
def le (x y : Exclusions) : Bool :=
  (x.flags.zip y.flags).all fun p => !p.1 || p.2

theorem flags_union (x y : Exclusions) : (x.union y).flags = List.zipWith (· || ·) x.flags y.flags := by
  cases x; cases y; rfl

/-- The flags that are set, by name, for messages. -/
def names (x : Exclusions) : List String :=
  (if x.interactive then ["interactive content"] else []) ++ (if x.media then ["media elements"] else []) ++
  (if x.heading then ["heading content"] else []) ++ (if x.sectioning then ["sectioning content"] else []) ++
  (if x.noscript then ["noscript"] else []) ++ (if x.dfn then ["dfn"] else []) ++
  (if x.meter then ["meter"] else []) ++ (if x.progress then ["progress"] else []) ++
  (if x.label then ["label"] else []) ++ (if x.form then ["form"] else []) ++
  (if x.table then ["table"] else []) ++ (if x.header then ["header"] else []) ++
  (if x.footer then ["footer"] else []) ++ (if x.address then ["address"] else []) ++
  (if x.a then ["a"] else [])

end Exclusions
end Whatwg.Html.Schema
